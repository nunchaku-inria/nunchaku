
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
  | Fi_functors of name * id * var list * (term list * id) list
  | Fi_predicates of name * id * var list * (term list * bool) list

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

let mk_fi_functors name vars l =
  let l = List.map Conv.as_ground_eqn_ l in
  let id = match l with
    | [] -> assert false
    | (id, _) :: _ -> id
  in
  Fi_functors (name, id, vars, List.map snd l)

let mk_fi_predicates name vars l =
  let l = List.map Conv.as_ground_atom_ l in
  let id = match l with
    | [] -> assert false
    | (id, _) :: _ -> id
  in
  Fi_predicates (name, id, vars, List.map snd l)

let pp_list_ pp = CCFormat.list ~sep:" " ~start:"" ~stop:"" pp

let rec pp_term out = function
  | Var v -> CCFormat.string out v
  | App (id,[]) -> CCFormat.string out id
  | App (id,l) ->
    Format.fprintf out "(@[%s@ %a@])" id (pp_list_ pp_term) l

let pp_statement out st =
  let pp_vars out = function
    | [] -> ()
    | vars -> Format.fprintf out "![@[%a@]]:@ " (pp_list_ CCFormat.string) vars
  in
  match st with
  | Fi_domain (_, v, l) ->
    Format.fprintf out "(@[<1>domain %s in@ [@[%a@]]@])."
      v (pp_list_ CCFormat.string) l
  | Fi_functors (_, id, vars, l) ->
    let pp_eqn out (args,rhs_id) =
      Format.fprintf out "(@[%s(%a)@ = %s@])" id (pp_list_ pp_term) args rhs_id
    in
    Format.fprintf out "(@[<1>functors for %s@ @[%a[@[%a@]]@]@])."
      id pp_vars vars (pp_list_ pp_eqn) l
  | Fi_predicates (_, id, vars, l) ->
    let pp_pred out args = Format.fprintf out "%s(%a)" id (pp_list_ pp_term) args in
    let pp_pred out (args,b) =
      if b then pp_pred out args else Format.fprintf out "(@[not@ %a@])" pp_pred args
    in
    Format.fprintf out "(@[<1>predicates for %s@ @[%a[@[%a@]]@]@])."
      id pp_vars vars (pp_list_ pp_pred) l

let pp_statements out =
  Format.fprintf out "[@[<hv>%a@]]"
    (CCFormat.list ~start:"" ~stop:"" ~sep:" " pp_statement)

(** {2 Conversion to Model} *)

let to_model
  : statement list -> (T.term, T.ty) Model.t
  = fun l ->
    let module M = Model in
    (* unfailing name -> ID *)
    let id_of_name_ i =
      try Some (ID.Erase.of_name T.erase i)
      with Not_found -> None
    in
    (* some names were not in the input, such as constants *)
    let get_or_create_id i =
      try ID.Erase.of_name T.erase i
      with Not_found ->
        let id = ID.make i in
        ID.Erase.add_name T.erase i id;
        id
    in
    (* convert a term back *)
    let rec term_to_tptp subst : term -> T.term
      = function
        | App (id, l) ->
          let subst _ = Conv.failf "no variable allowed in sub-term under %s" id in
          T.app (get_or_create_id id) (List.map (term_to_tptp subst) l)
        | Var v -> subst v
    in
    (* convert a list of cases into a Model.DT *)
    let cases_to_dt ~rhs_to_term id input_vars l =
      (* create fresh variables *)
      let vars = match l with
        | [] -> assert false
        | (args, _) :: _ ->
          List.mapi (fun i _ -> Var.makef ~ty:T.Unitype "v%d" i) args
      in
      assert (List.length vars >= List.length input_vars);
      if vars=[]
      then match l with
        | [[], rhs] -> `Const (rhs_to_term rhs)
        | _ -> assert false
      else (
        let l =
          List.map
            (fun (args,rhs) ->
               assert (List.length args = List.length vars);
               let vars_seen = ref [] in
               (* map members of [input_vars] to [vars] *)
               let subst i v =
                 if List.mem v !vars_seen
                 then Conv.failf "variable %s occurs non-linearly" v
                 else if List.mem v input_vars
                 then T.var (List.nth vars i)
                 else Conv.failf "variable %s not in scope" v
               in
               let args = List.mapi (fun i -> term_to_tptp (subst i)) args in
               let rhs = rhs_to_term rhs in
               let conds = List.combine vars args in
               conds, rhs)
            l
        in
        let else_ = T.undefined (T.app id (List.map T.var vars)) in
        let dt = M.DT.test l ~else_ in
        `Fun (vars, dt)
      )
    in
    List.fold_left
      (fun m st -> match st with
         | Fi_domain (_, _, l) ->
           (* trivial domain *)
           let l = List.map get_or_create_id l in
           M.add_finite_type m T.Unitype l
         | Fi_functors (_, name, vars, l) ->
           begin match id_of_name_ name with
             | None ->
               Utils.debugf 2 "failed to map `%s` to a known ID" (fun k->k name);
               m
             | Some id ->
               begin match
                   cases_to_dt id vars l
                     ~rhs_to_term:(fun rhs -> T.const (get_or_create_id rhs))
                 with
                   | `Const rhs -> M.add_const m (T.const id, rhs, M.Symbol_fun)
                   | `Fun (vars, dt) ->
                     M.add_fun m (T.const id, vars, dt, M.Symbol_fun)
               end
           end
         | Fi_predicates (_, name, vars, l) ->
           begin match id_of_name_ name with
             | None ->
               Utils.debugf 2 "failed to map `%s` to a known ID" (fun k->k name);
               m
             | Some id ->
               begin match
                   cases_to_dt id vars l
                     ~rhs_to_term:(fun b -> if b then T.true_ else T.false_)
                 with
                   | `Const rhs -> M.add_const m (T.const id, rhs, M.Symbol_prop)
                   | `Fun (vars, dt) ->
                     M.add_fun m (T.const id, vars, dt, M.Symbol_prop)
               end
           end
      )
      M.empty
      l
