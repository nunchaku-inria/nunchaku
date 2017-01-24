
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Variables for Mutable Unification} *)

type id = ID.t

(** Pointer to another type *)
type 'a t = private {
  id : id;
  mutable deref : 'a option;
}

val make : name:string -> 'a t
(** New reference, with a fresh ID *)

val id : _ t -> id
(** Id of the variable *)

val equal : 'a t -> 'a t -> bool
(** Name equality (ignores the [deref] field) *)

val deref : 'a t -> 'a option
(** Access the content *)

val can_bind : _ t -> bool
(** [can_bind t] returns [true]  iff [t.deref = None] *)

val bound : _ t -> bool
(** [bound v] is [not (can_bind v)] *)

val bind : var:'a t -> 'a -> unit
(** [bind ~var t] binds [ref] to [t]. From now on,
    the holder of [ref] should behave like [t] in all aspects.
    @raise Invalid_argument if [var] is already bound *)

val rebind : var:'a t -> 'a -> unit
(** re-bind an already bound reference (for instance, for path compression).
    @raise Invalid_argument if the ref is not bound *)

val update : f:('a -> 'b) -> 'a t -> 'b t
(** Update the linked content, if any *)

val pp : Format.formatter -> _ t -> unit
val to_string : _ t -> string


