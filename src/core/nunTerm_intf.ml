
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 View for terms} *)

module ID = NunID
module Var = NunVar

type id = NunID.t
type 'a var = 'a NunVar.t

type ('a, 'ty) view =
  | Builtin of NunBuiltin.T.t (** built-in symbol *)
  | Const of id (** top-level symbol *)
  | Var of 'ty var (** bound variable *)
  | App of 'a * 'a list
  | Fun of 'ty var * 'a
  | Forall of 'ty var * 'a
  | Exists of 'ty var * 'a
  | Let of 'ty var * 'a * 'a
  | Ite of 'a * 'a * 'a
  | Eq of 'a * 'a
  | TyKind
  | TyType
  | TyBuiltin of NunBuiltin.Ty.t (** Builtin type *)
  | TyArrow of 'ty * 'ty   (** Arrow type *)
  | TyForall of 'ty var * 'ty  (** Polymorphic/dependent type *)
  | TyMeta of 'ty NunMetaVar.t

(* NOTE: Eq has its own case, because its type parameter is often hidden.
   For instance, when we parse a model back from TPTP or SMT, equalities
   are not annotated with their type parameter; we would have to compute or
   infer types again for an unclear benefit (usually just for printing).

   Instead, we just consider equality  to be a specific "ad-hoc polymorphic"
   predicate and do not require it to have a type argument.
 *)

module type VIEW = sig
  type t
  type ty

  val view : t -> (t, ty) view
end

module type VIEW_SAME_TY = sig
  type t
  type ty = t

  val view : t -> (t, ty) view
end

(** {2 Utils} *)

module Util(T : VIEW_SAME_TY) : sig
  val to_seq : T.t -> T.t Sequence.t
  (** Iterate on sub-terms *)

  val to_seq_vars : T.t -> T.ty var Sequence.t
  (** Iterate on variables *)

  val free_meta_vars :
    ?init:T.ty NunMetaVar.t NunID.Map.t ->
    T.t ->
    T.ty NunMetaVar.t NunID.Map.t
  (** The free type meta-variables in [t] *)
end = struct
  let to_seq t yield =
    let rec aux t =
      yield t;
      match T.view t with
      | TyKind
      | TyType
      | TyBuiltin _
      | TyMeta _
      | Builtin _
      | Const _ -> ()
      | Var v -> aux (Var.ty v)
      | App (f,l) -> aux f; List.iter aux l
      | Fun (v,t)
      | TyForall (v,t)
      | Forall (v,t)
      | Exists (v,t) -> aux (Var.ty v); aux t
      | Let (v,t,u) -> aux (Var.ty v); aux t; aux u
      | Ite (a,b,c) -> aux a; aux b; aux c
      | Eq (a,b) -> aux a; aux b
      | TyArrow (a,b) -> aux a; aux b
    in
    aux t

  let to_seq_vars t =
    to_seq t
    |> Sequence.filter_map
        (fun t -> match T.view t with
          | Var v
          | Forall (v,_)
          | Exists (v,_)
          | TyForall (v,_)
          | Let (v,_,_)
          | Fun (v,_) -> Some v
          | Builtin _
          | Const _
          | App (_,_)
          | Ite (_,_,_)
          | Eq (_,_)
          | TyKind
          | TyType
          | TyBuiltin _
          | TyArrow (_,_)
          | TyMeta _ -> None
        )

  let to_seq_meta_vars t =
    to_seq t
    |> Sequence.filter_map
        (fun t -> match T.view t with
          | TyMeta v -> Some v
          | Var _
          | Forall (_,_)
          | Exists (_,_)
          | TyForall (_,_)
          | Let (_,_,_)
          | Fun (_,_)
          | Builtin _
          | Const _
          | App (_,_)
          | Ite (_,_,_)
          | Eq (_,_)
          | TyKind
          | TyType
          | TyBuiltin _
          | TyArrow (_,_) -> None
        )

  let free_meta_vars ?(init=ID.Map.empty) t =
    to_seq_meta_vars t
      |> Sequence.fold
          (fun acc v -> ID.Map.add (NunMetaVar.id v) v acc)
          init
end
