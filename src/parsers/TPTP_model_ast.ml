
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Simple Model AST} *)

open Nunchaku_core

module Fmt = CCFormat
module T = FO_tptp

type name = string
type id = string
type var = string

type term =
  | App of id * term list
  | Var of var
  | Forall of var * term
  | And of term * term
  | Or of term * term
  | Not of term
  | Atom of term
  | Eq of term * term
  | Equiv of term * term
  | True
  | False

type statement =
  | Fi_domain of name * var * id list (* forall X. X=a1 | ... | X=an *)
  | Fi_functors of name * id * var list * (var list * term list * term) list
  | Fi_predicates of name * id * var list * (var list * term list * term) list

let rec pp out = function
  | Var v -> Fmt.string out v
  | App (c,[]) -> Fmt.string out c
  | App (c,l) ->
    Fmt.fprintf out "(@[<2>%a@ %a@])" Fmt.string c (Utils.pp_list ~sep:" " pp) l
  | True -> Fmt.string out "true"
  | False -> Fmt.string out "false"
  | Not t -> Fmt.fprintf out "(@[not@ %a@])" pp t
  | And (t,u) -> Fmt.fprintf out "(@[and@ %a@ %a@])" pp t pp u
  | Or (t,u) -> Fmt.fprintf out "(@[or@ %a@ %a@])" pp t pp u
  | Eq (t,u) -> Fmt.fprintf out "(@[= %a %a@])" pp t pp u
  | Equiv (t,u) -> Fmt.fprintf out "(@[<=>@ %a@ %a@])" pp t pp u
  | Forall (v,t) ->
    Fmt.fprintf out "(@[forall %a@ %a@])" Fmt.string v pp t
  | Atom t -> pp out t

let var v = Var v
let app id l = App (id,l)
let const id = app id []

let forall v f = Forall (v,f)
let forall_l = List.fold_right forall
let or_ a b = Or(a,b)
let and_ a b = And(a,b)
let not_ = function
  | True -> False
  | False -> True
  | a -> Not a
let eq a b = Eq(a,b)
let equiv a b = Equiv(a,b)
let atom t = Atom t
let true_ = True
let false_ = False

let rec open_forall = function
  | Forall (v,f) ->
    let vars, f' = open_forall f in
    v :: vars, f'
  | t -> [], t

let failf ?loc m = Parsing_utils.parse_error_ ?loc m

let rec as_or_ ?loc = function
  | Or (a,b) -> List.rev_append (as_or_ ?loc a) (as_or_ ?loc b)
  | (Atom _ | Eq _ | Equiv (_,_) | Forall (_,_) | Not _) as f -> [f]
  | t -> failf ?loc "expected disjunction,@ got `%a`" pp t

let rec as_and_ ?loc = function
  | And (a,b) -> List.rev_append (as_and_ ?loc a) (as_and_ ?loc b)
  | (Atom _ | Eq _ | Equiv (_,_) | Forall (_,_) | Not _) as f -> [f]
  | t -> failf ?loc "expected conjunction,@ got `%a`" pp t

module Conv = struct
  let as_forall_ = function
    | Forall (v,f) -> v, f
    | _ -> failf "expected forall"

  let as_id_eqn_of_ v = function
    | Eq (Var v', App (rhs, _)) when v=v' -> rhs
    | t -> failf "expected equation with LHS=%s,@ got `%a`" v pp t

  let as_ground_term_ = function
    | App (id, args) -> id, args
    | t -> failf "expected ground term,@ got `%a`" pp t

  let as_eqn_ ?loc t =
    let vars, t = open_forall t in
    match t with
      | Eq (lhs,rhs) ->
        let id, args = as_ground_term_ lhs in
        id, (vars, args, rhs)
      | _ -> failf ?loc "expected equation,@ got `%a`" pp t

  let as_atom_ ?loc t =
    let vars, t = open_forall t in
    let rec aux = function
      | Not f ->
        let id, (vars, args, rhs) = aux f in
        id, (vars, args, not_ rhs)
      | Atom (App (id, args)) ->
        id, (vars, args, true_)
      | Equiv (lhs, rhs) ->
        let id, args = as_ground_term_ lhs in
        id, (vars, args, rhs)
      | t -> failf ?loc "expected signed atom,@ got `%a`" pp t
    in
    aux t
end

let mk_fi_domain ?loc name (f:term) : statement =
  let v, l = Conv.as_forall_ f in
  let l = List.map (Conv.as_id_eqn_of_ v) (as_or_ ?loc l) in
  Fi_domain (name, v, l)

let mk_fi_functors ?loc name vars (l:term list) : statement =
  let l = List.map (Conv.as_eqn_ ?loc) l in
  let id = match l with
    | [] -> assert false
    | (id, _) :: _ -> id
  in
  Fi_functors (name, id, vars, List.map snd l)

let mk_fi_predicates ?loc name vars (l:term list) : statement =
  let l = List.map (Conv.as_atom_ ?loc) l in
  let id = match l with
    | [] -> assert false
    | (id, _) :: _ -> id
  in
  Fi_predicates (name, id, vars, List.map snd l)

let pp_list_ pp = Utils.pp_list ~sep:" " pp

let rec pp_term out = function
  | Var v -> CCFormat.string out v
  | App (id,[]) -> CCFormat.string out id
  | App (id,l) -> Format.fprintf out "(@[%s@ %a@])" id (pp_list_ pp_term) l
  | Forall (v,f) -> Format.fprintf out "(@[forall %s.@ %a@])" v pp_term f
  | And (a,b) -> Format.fprintf out "(@[and %a@ %a@])" pp_term a pp_term b
  | Or (a,b)-> Format.fprintf out "(@[or@ %a@ %a@])" pp_term a pp_term b
  | Not t -> Format.fprintf out "(@[not@ %a@])" pp_term t
  | Atom t -> pp_term out t
  | Eq (a,b) -> Format.fprintf out "(@[=@ %a@ %a@])" pp_term a pp_term b
  | Equiv (a,b) -> Format.fprintf out "(@[<=>@ %a@ %a@])" pp_term a pp_term b
  | True -> CCFormat.string out "true"
  | False -> CCFormat.string out "false"

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
      let pp_eqn out (vars',args,rhs) =
        Format.fprintf out "(@[%a%s(%a)@ = %a@])"
          pp_vars vars' id (pp_list_ pp_term) args pp_term rhs
      in
      Format.fprintf out "(@[<1>functors for %s@ @[%a[@[%a@]]@]@])."
        id pp_vars vars (pp_list_ pp_eqn) l
    | Fi_predicates (_, id, vars, l) ->
      let pp_pred out args = Format.fprintf out "%s(%a)" id (pp_list_ pp_term) args in
      let pp_pred out (vars',args,rhs) =
        Format.fprintf out "(%a@[%a <=> %a@])" pp_vars vars' pp_pred args pp_term rhs
      in
      Format.fprintf out "(@[<1>predicates for %s@ @[%a[@[%a@]]@]@])."
        id pp_vars vars (pp_list_ pp_pred) l

let pp_statements out =
  Format.fprintf out "[@[<hv>%a@]]"
    (Utils.pp_list ~sep:" " pp_statement)

(** {2 Conversion to Model} *)

let to_model (l:statement list) : (T.term, T.ty) Model.t =
  let module M = Model in
  (* unfailing name -> ID *)
  let id_of_name_ i : ID.t option =
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
  let rec term_to_tptp subst (t:term) : T.term = match t with
    | App (id, l) ->
      T.app (get_or_create_id id) (List.map (term_to_tptp subst) l)
    | Var v -> subst v
    | True -> T.true_
    | False -> T.false_
    | _ -> failf "cannot convert `@[%a@]` to term" pp_term t
  in
  (* convert a list of cases into a Model.DT *)
  let cases_to_dt input_vars l =
    (* create fresh variables *)
    let vars = match l with
      | [] -> assert false
      | (_, args, _) :: _ ->
        List.mapi (fun i _ -> Var.makef ~ty:T.Unitype "v%d" i) args
    in
    assert (List.length vars >= List.length input_vars);
    if vars=[]
    then match l with
      | [_, [], rhs] ->
        let subst v = failf "variable %s not in scope" v in
        M.DT.yield (term_to_tptp subst rhs)
      | _ -> assert false
    else (
      let l =
        List.map
          (fun (input_vars',args,rhs) ->
             assert (List.length args = List.length vars);
             let vars_seen = ref [] in
             (* map members of [input_vars] to [vars] *)
             let subst i v =
               if List.mem_assoc v !vars_seen
               then List.assoc v !vars_seen
               else if (List.mem v input_vars || List.mem v input_vars') && i>=0
               then (
                 let v' = T.var (List.nth vars i) in
                 vars_seen := (v, v') :: !vars_seen;
                 v'
               )
               else failf "variable %s not in scope" v
             in
             let args = List.mapi (fun i -> term_to_tptp (subst i)) args in
             let rhs = term_to_tptp (subst ~-1) rhs in
             let conds = List.map2 M.DT.mk_flat_test vars args in
             conds, rhs)
          l
      in
      let fdt =
        { M.DT.
          fdt_vars=vars;
          fdt_cases=l;
          fdt_default=None; (* should be complete *)
        } in
      M.DT.of_flat ~equal:T.term_equal ~hash:T.term_hash fdt
    )
  in
  (* add one statement to the model *)
  let add_st m st : (_,_) M.t = match st with
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
          let dt = cases_to_dt vars l in
          M.add_value m (T.const id, dt, M.Symbol_fun)
      end
    | Fi_predicates (_, name, vars, l) ->
      begin match id_of_name_ name with
        | None ->
          Utils.debugf 2 "failed to map `%s` to a known ID" (fun k->k name);
          m
        | Some id ->
          let dt = cases_to_dt vars l in
          M.add_value m (T.const id, dt, M.Symbol_prop)
      end
  in
  List.fold_left add_st M.empty l
