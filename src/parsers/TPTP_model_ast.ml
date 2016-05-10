
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Simple Model AST} *)

open Nunchaku_core

module T = FO_tptp

type name = string
type id = string
type var = string

type term =
  | App of id * term list
  | Var of var

type form =
  | Forall of var * form
  | And of form * form
  | Or of form * form
  | Not of form
  | Atom of term
  | Eq of term * term
  | True
  | False

type statement =
  | Fi_domain of name * var * id list (* forall X. X=a1 | ... | X=an *)
  | Fi_functors of name * id * (term list * id) list
  | Fi_predicates of name * id * (term list * bool) list

let var v = Var v
let app id l = App (id,l)
let const id = app id []

let forall v f = Forall (v,f)
let or_ a b = Or(a,b)
let and_ a b = And(a,b)
let not_ a = Not a
let eq a b = Eq(a,b)
let atom t = Atom t
let true_ = True
let false_ = False

module Conv = struct
  let failf m = Parsing_utils.parse_error_ m

  let as_forall_ = function
    | Forall (v,f) -> v, f
    | _ -> failf "expected forall"

  let rec as_or_ = function
    | Or (a,b) -> List.rev_append (as_or_ a) (as_or_ b)
    | (Atom _ | Eq _ ) as f -> [f]
    | _ -> failf "expected conjunction"

  let as_id_eqn_of_ v = function
    | Eq (Var v', App (rhs, _)) when v=v' -> rhs
    | _ -> failf "expected equation with LHS=%s" v

  let as_ground_eqn_ = function
    | App (id, args), App (rhs, []) -> id, (args,rhs)
    | _ -> failf "expected equation with constant LHS"

  let rec as_ground_atom_ = function
    | Not f ->
      let id, (args, b) = as_ground_atom_ f in
      id, (args, not b)
    | Atom (App (id, args)) ->
      id, (args, true)
    | _ -> failf "expected signed atom"
end

let mk_fi_domain name f =
  let v, l = Conv.as_forall_ f in
  let l = List.map (Conv.as_id_eqn_of_ v) (Conv.as_or_ l) in
  Fi_domain (name, v, l)

let mk_fi_functors name l =
  let l = List.map Conv.as_ground_eqn_ l in
  let id = match l with
    | [] -> assert false
    | (id, _) :: _ -> id
  in
  Fi_functors (name, id, List.map snd l)

let mk_fi_predicates name l =
  let l = List.map Conv.as_ground_atom_ l in
  let id = match l with
    | [] -> assert false
    | (id, _) :: _ -> id
  in
  Fi_predicates (name, id, List.map snd l)

let pp_list_ pp = CCFormat.list ~sep:" " ~start:"" ~stop:"" pp

let rec pp_term out = function
  | Var v -> CCFormat.string out v
  | App (id,[]) -> CCFormat.string out id
  | App (id,l) ->
    Format.fprintf out "(@[%s@ %a@])" id (pp_list_ pp_term) l

let pp_statement out = function
  | Fi_domain (_, v, l) ->
    Format.fprintf out "(@[<1>domain %s in@ [@[%a@]]@])."
      v (pp_list_ CCFormat.string) l
  | Fi_functors (_, id, l) ->
    let pp_eqn out (args,rhs_id) =
      Format.fprintf out "(@[%s(%a)@ = %s@])" id (pp_list_ pp_term) args rhs_id
    in
    Format.fprintf out "(@[<1>functors for %s@ [@[%a@]]@])." id (pp_list_ pp_eqn) l
  | Fi_predicates (_, id, l) ->
    let pp_pred out args = Format.fprintf out "%s(%a)" id (pp_list_ pp_term) args in
    let pp_pred out (args,b) =
      if b then pp_pred out args else Format.fprintf out "(@[not@ %a@])" pp_pred args
    in
    Format.fprintf out "(@[<1>predicates for %s@ [@[%a@]]@])." id (pp_list_ pp_pred) l

let pp_statements out =
  Format.fprintf out "[@[<hv>%a@]]"
    (CCFormat.list ~start:"" ~stop:"" ~sep:" " pp_statement)

(** {2 Conversion to Model} *)

let to_model
  : statement list -> (T.term, T.ty) Model.t
  = fun l ->
    let module M = Model in
    let id_of_name_ = ID.Erase.of_name T.erase in
    (* some names were not in the input, such as constants *)
    let get_or_create_id i =
      try id_of_name_ i
      with Not_found ->
        let id = ID.make i in
        ID.Erase.add_name T.erase i id;
        id
    in
    (* convert a term back *)
    let rec term_to_tptp : term -> T.term
      = function
        | App (id, l) -> T.app (id_of_name_ id) (List.map term_to_tptp l)
        | Var _ -> assert false
    in
    (* convert a list of cases into a Model.DT *)
    let cases_to_dt ~rhs_to_term id l =
      (* create fresh variables *)
      let vars = match l with
        | [] -> assert false
        | (args, _) :: _ ->
          List.mapi (fun i _ -> Var.makef ~ty:T.Unitype "v%d" i) args
      in
      let l =
        List.map
          (fun (args,rhs) ->
             assert (List.length args = List.length vars);
             let args = List.map term_to_tptp args in
             let rhs = rhs_to_term rhs in
             let conds = List.combine vars args in
             conds, rhs)
          l
      in
      let else_ = T.undefined (T.app id (List.map T.var vars)) in
      let dt = M.DT.test l ~else_ in
      vars, dt
    in
    List.fold_left
      (fun m st -> match st with
         | Fi_domain (_, _, l) ->
           (* trivial domain *)
           let l = List.map get_or_create_id l in
           M.add_finite_type m T.Unitype l
         | Fi_functors (_, name, l) ->
           let id = id_of_name_ name in
           let vars, dt =
             cases_to_dt id l
               ~rhs_to_term:(fun rhs -> T.const (id_of_name_ rhs))
           in
           M.add_fun m (T.const id, vars, dt, M.Symbol_fun)
         | Fi_predicates (_, name, l) ->
           let id = id_of_name_ name in
           let vars, dt =
             cases_to_dt id l
               ~rhs_to_term:(fun b -> if b then T.true_ else T.false_)
           in
           M.add_fun m (T.const id, vars, dt, M.Symbol_prop)
      )
      M.empty
      l
