
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 View for terms} *)

module ID = NunID
module Var = NunVar
module M = NunMark

type id = NunID.t
type 'a var = 'a NunVar.t

type _ binder =
  | Forall
  | Exists
  | Fun
  | TyForall : M.polymorph binder

type 'a case = 'a var list * 'a
(** A pattern match case for a given constructor [ vars, right-hand side ]
    The pattern must be linear (variable list does not contain duplicates) *)

(** A list of cases (indexed by constructor) *)
type 'a cases = 'a case ID.Map.t

let cases_to_list = ID.Map.to_list

(* check that: each case is linear (all vars are different) *)
let cases_well_formed (type a) m =
  let is_linear_ _ (vars,_) =
    let module VarSet = Var.Set(struct type t = a end) in
    VarSet.cardinal (VarSet.of_list vars) = List.length vars
  in
  ID.Map.for_all is_linear_ m

type ('a, 'inv) view =
  | Const of id (** top-level symbol *)
  | Var of 'a var (** bound variable *)
  | App of 'a * 'a list
  | AppBuiltin of NunBuiltin.T.t * 'a list (** built-in operation *)
  | Bind :
      'inv_b binder
      * 'a var
      * 'a
      -> ('a, <poly:'inv_b; ..>) view
  | Let of 'a var * 'a * 'a
  | Match of 'a * 'a cases (** shallow pattern-match *)
  | TyVar :
      'a var
      -> ('a, <poly:NunMark.polymorph;..>) view
  | TyBuiltin of NunBuiltin.Ty.t (** Builtin type *)
  | TyArrow of 'a * 'a  (** Arrow type *)
  | TyMeta :
      'a NunMetaVar.t ->
      ('a, <meta:M.with_meta; poly:_>) view

(* NOTE: Eq has its own case (in Builtin), because its type parameter is often hidden.
   For instance, when we parse a model back from TPTP or SMT, equalities
   are not annotated with their type parameter; we would have to compute or
   infer types again for an unclear benefit (usually just for printing).

   Instead, we just consider equality  to be a specific "ad-hoc polymorphic"
   predicate and do not require it to have a type argument.
 *)

type ('t, 'inv) repr = 't -> ('t, 'inv) view
(** A concrete representation of terms by the type [t'] *)

type ('t, 'inv) build = ('t, 'inv) view -> 't
(** A builder for a concrete representation with type ['t]. *)

(** {2 Utils} *)

(** Search for a head symbol
    @raise Not_found if not an application/const *)
let rec head_sym
: type t inv. repr:(t,inv) repr -> t -> ID.t
= fun ~repr t -> match repr t with
  | App (f, _) -> head_sym ~repr f
  | Const id -> id
  | _ -> raise Not_found

(** Iterate on sub-terms *)
let to_seq
: type t inv. repr:(t,inv) repr -> t -> t Sequence.t
= fun ~repr t yield ->
  let rec aux t =
    yield t;
    match repr t with
    | TyMeta _ -> ()
    | TyVar _ -> ()
    | TyBuiltin _
    | AppBuiltin _
    | Const _ -> ()
    | Var v -> aux_var v
    | Match (t,l) ->
        aux t;
        ID.Map.iter (fun _ (vars,rhs) -> List.iter aux_var vars; aux rhs) l
    | App (f,l) -> aux f; List.iter aux l
    | Bind (_,v,t) -> aux (Var.ty v); aux t
    | Let (v,t,u) -> aux (Var.ty v); aux t; aux u
    | TyArrow (a,b) -> aux a; aux b
  and aux_var v = aux (Var.ty v)
  in
  aux t

(** Iterate on free variables. Only for terms that have meta-variables. *)
let to_seq_free_vars
: type t. repr:(t,(<meta:M.with_meta;..> as 'inv)) repr -> t -> t var Sequence.t
= fun (type t_) ~repr t yield ->
  let module VarSet = Var.Set(struct type t = t_ end) in
  let rec aux ~bound (t:t_) = match repr t with
    | Const _ -> ()
    | TyVar v ->
        if VarSet.mem v bound then () else yield v
    | Var v ->
        if VarSet.mem v bound then () else yield v
    | App (f,l) ->
        aux ~bound f; List.iter (aux ~bound) l
    | Match (t,l) ->
        aux ~bound t;
        ID.Map.iter
          (fun _ (vars,rhs) ->
            let bound = List.fold_right VarSet.add vars bound in
            aux ~bound rhs
          ) l
    | AppBuiltin (_,l) -> List.iter (aux ~bound) l
    | Bind (_,v,t) -> aux ~bound:(VarSet.add v bound) t
    | Let (v,t,u) -> aux ~bound t; aux ~bound:(VarSet.add v bound) u
    | TyBuiltin _ -> ()
    | TyArrow (a,b) -> aux ~bound a; aux ~bound b
    | TyMeta _ -> ()
  in
  aux ~bound:VarSet.empty t

(** Iterate on variables *)
let to_seq_vars
: type t inv. repr:(t,inv) repr -> t -> t var Sequence.t
= fun ~repr t ->
  to_seq ~repr t
  |> Sequence.flat_map
      (fun (t:t) -> match repr t with
        | TyVar v -> Sequence.return v
        | Var v -> Sequence.return v
        | Bind (_,v,_) -> Sequence.return v
        | Let (v,_,_) -> Sequence.return v
        | Match (_,l) ->
            let open Sequence.Infix in
            ID.Map.to_seq l >>= fun (_,(vars,_)) -> Sequence.of_list vars
        | AppBuiltin _
        | Const _
        | App _
        | TyBuiltin _
        | TyArrow (_,_) -> Sequence.empty
        | TyMeta _ -> Sequence.empty
      )

let to_seq_meta_vars (type t) ~repr (t:t) =
  to_seq ~repr t
  |> Sequence.filter_map
      (fun t -> match repr t with
        | TyMeta v -> Some v
        | TyVar _ -> None
        | Var _
        | Bind _
        | AppBuiltin _
        | Const _
        | Let _
        | Match _
        | App _
        | TyBuiltin _
        | TyArrow (_,_) -> None
      )

(** The free type meta-variables in [t] *)
let free_meta_vars
: type t.
  ?init:t NunMetaVar.t NunID.Map.t ->
  repr:(t, (<meta:M.with_meta;poly:_> as 'inv)) repr ->
  t ->
  t NunMetaVar.t NunID.Map.t
= fun ?(init=ID.Map.empty) ~repr t ->
  to_seq_meta_vars ~repr t
    |> Sequence.fold
        (fun acc v -> ID.Map.add (NunMetaVar.id v) v acc)
        init
