
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 References for Unification} *)

(** Pointer to another type *)
type 'a t = private {
  mutable deref : 'a option;
}

val create : unit -> 'a t
(** New reference *)

val deref : 'a t -> 'a option
(** Access the content *)

val can_bind : _ t -> bool
(** [can_bind t] returns [true]  iff [t.deref = None] *)

val bind : ref:'a t -> 'a -> unit
(** [bind ~ref t] binds [ref] to [t]. From now on,
    the holder of [ref] should behave like [t] in all aspects.
    @raise Invalid_argument if [ref] is already bound *)


val rebind : ref:'a t -> 'a -> unit
(** re-bind an already bound reference (for instance, for path compression).
    @raise Invalid_argument if the ref is not bound *)
