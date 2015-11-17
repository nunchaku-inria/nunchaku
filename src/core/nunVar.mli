
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Variable} *)

type id = NunID.t

type +'ty t = private {
  id: id;
  ty: 'ty;
}

val equal : 'a t -> 'a t -> bool
(** Equality, purely by identifier. It is impossible to forge two variables
    with the same identifier but distinct types *)

val compare : 'a t -> 'a t -> int
(** Total order based on {!id} *)

val make : ty:'ty -> name:string -> 'ty t
(** [make ~ty ~name] makes a new variable with the given name and type. It
    will have a unique identifier *)

val fresh_copy : 'ty t -> 'ty t
(** [fresh_copy v] makes a variable that looks like [v] but has a fresh
    identifier *)

val fresh_copies : 'ty t list -> 'ty t list
(** Fresh copy each element of the list *)

val of_id : ty:'ty -> id -> 'ty t
(** [of_id ~ty id] makes a variable with the given ID *)

val ty : 'ty t -> 'ty

val id : _ t -> id

val name : _ t -> string

val update_ty : 'a t -> f:('a -> 'b) -> 'b t
(** Update the type, and make a new variable with it with {b THE SAME ID}.
    Careful not to break invariants. *)

val fresh_update_ty : 'a t -> f:('a -> 'b) -> 'b t
(** Update the type, and make a new variable with it with a fresh ID. *)

val print : Format.formatter -> _ t -> unit
val to_string : _ t -> string

(** {2 Substitutions} *)

module Subst : sig
  type 'a var = 'a t

  type ('ty, 'a) t
  (** A substitution for variables of type ['ty], to terms ['a] *)

  val empty : _ t
  val is_empty : _ t -> bool

  val add : subst:('ty,'a) t -> 'ty var -> 'a -> ('ty,'a) t

  val add_list : subst:('ty,'a) t -> 'ty var list -> 'a list -> ('ty,'a) t
  (** [add_list ~subst v t] add each binding [v_i -> t_i] to the subst.
      @raise Invalid_argument if [List.length v <> List.length t] *)

  val remove : subst:('ty,'a) t -> 'ty var -> ('ty,'a) t
  (** Remove binding for this variable.
      {b careful} if other bindings depend on this variable's binding... *)

  val mem : subst:('ty,'a) t -> 'ty var -> bool
  val find : subst:('ty,'a) t -> 'ty var -> 'a option
  val find_exn : subst:('ty,'a) t -> 'ty var -> 'a  (** @raise Not_found if var not bound *)

  val to_list : ('ty,'a) t -> ('ty var * 'a) list
end

(** {2 Data structures} *)

module Set(Ty : sig type t end) : CCSet.S with type elt = Ty.t t


