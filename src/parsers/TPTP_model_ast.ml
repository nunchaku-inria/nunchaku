
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Simple Model AST} *)

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
