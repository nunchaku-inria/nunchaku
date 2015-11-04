
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
      -> ('a, <poly:'inv_b; meta:_>) view
  | Let of 'a var * 'a * 'a
  | Match of 'a * 'a cases (** shallow pattern-match *)
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

module type VIEW = sig
  type 'inv t
  type 'inv ty = 'inv t

  val view : 'inv t -> ('inv t, 'inv) view
end

(** {2 Utils} *)

module Util(T : VIEW) : sig
  val to_seq : 'inv T.t -> 'inv T.t Sequence.t
  (** Iterate on sub-terms *)

  val to_seq_vars : 'inv T.t -> 'inv T.ty var Sequence.t
  (** Iterate on variables *)

  val to_seq_free_vars : (<meta:M.with_meta;..> as 'inv) T.t -> 'inv T.ty var Sequence.t
  (** Iterate on free variables. Only for terms that have meta-variables. *)

  val head_sym : _ T.t -> id
  (** Search for a head symbol
      @raise Not_found if not an application/const *)

  val free_meta_vars :
    ?init:(<meta:M.with_meta;poly:_> as 'inv) T.ty NunMetaVar.t NunID.Map.t ->
    'inv T.t ->
    'inv T.ty NunMetaVar.t NunID.Map.t
  (** The free type meta-variables in [t] *)
end = struct
  let rec head_sym t = match T.view t with
    | App (f, _) -> head_sym f
    | Const id -> id
    | _ -> raise Not_found

  let to_seq (type inv) (t:inv T.t) (yield:inv T.t -> unit) : unit =
    let rec aux (t:inv T.t) : unit =
      yield t;
      match T.view t with
      | TyMeta _ -> ()
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

  let to_seq_free_vars (type inv) (t:inv T.t) yield =
    let module VarSet = Var.Set(struct type t = inv T.ty end) in
    let rec aux ~bound (t:inv T.t) = match T.view t with
      | Const _ -> ()
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

  let to_seq_vars (type inv) (t:inv T.t) =
    to_seq t
    |> Sequence.flat_map
        (fun (t:inv T.t) -> match T.view t with
          | Var v -> Sequence.return v
          | Bind (_,v,_) -> Sequence.return v
          | Let (v,_,_) -> Sequence.return v
          | Match (_,l) ->
              let open Sequence.Infix in
              ID.Map.to_seq l >>= fun (_,(vars,_)) -> Sequence.of_list vars
          | AppBuiltin _
          | Const _
          | App (_,_)
          | TyBuiltin _
          | TyArrow (_,_) -> Sequence.empty
          | TyMeta _ -> Sequence.empty
        )

  let to_seq_meta_vars t =
    to_seq t
    |> Sequence.filter_map
        (fun t -> match T.view t with
          | TyMeta v -> Some v
          | Var _
          | Bind _
          | AppBuiltin _
          | Const _
          | Let _
          | Match _
          | App (_,_)
          | TyBuiltin _
          | TyArrow (_,_) -> None
        )

  let free_meta_vars ?(init=ID.Map.empty) t =
    to_seq_meta_vars t
      |> Sequence.fold
          (fun acc v -> ID.Map.add (NunMetaVar.id v) v acc)
          init
end
