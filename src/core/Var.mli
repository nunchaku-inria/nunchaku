
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Variable} *)

type id = ID.t

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

val makef : ty:'ty -> ('b, Format.formatter, unit, 'ty t) format4 -> 'b
(** printf-ready make function *)

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

val set_ty : 'a t -> ty:'b -> 'b t
(** Change the type of the variable *)

val fresh_update_ty : 'a t -> f:('a -> 'b) -> 'b t
(** Update the type, and make a new variable with it with a fresh ID. *)

val make_gen : names:(int -> string, unit, string) format -> 'a -> 'a t
(** [make_gen ~names] creates a new generator of fresh variables
    whose names follow the naming scheme [names] (a formatter with one "%d") *)

val print : _ t CCFormat.printer
val to_string : _ t -> string

val print_full : _ t CCFormat.printer

(** {2 Substitutions} *)

module Subst : sig
  type 'a var = 'a t

  type (+'ty, +'a) t
  (** A substitution for variables of type ['ty], to terms ['a] *)

  val empty : _ t
  val is_empty : _ t -> bool
  val size : _ t -> int

  val singleton : 'ty var -> 'a -> ('ty, 'a) t

  val add : subst:('ty,'a) t -> 'ty var -> 'a -> ('ty,'a) t

  val add_list : subst:('ty,'a) t -> 'ty var list -> 'a list -> ('ty,'a) t
  (** [add_list ~subst v t] add each binding [v_i -> t_i] to the subst.
      @raise Invalid_argument if [List.length v <> List.length t] *)

  val concat : ('ty,'a) t -> into:('ty,'a) t -> ('ty,'a) t
  (** [concat s ~into:s2] adds every binding of [s] into [s2] *)

  val of_list : 'ty var list -> 'a list -> ('ty,'a) t
  (** [of_list vars l = add_list ~subst:empty vars l] *)

  val remove : subst:('ty,'a) t -> 'ty var -> ('ty,'a) t
  (** Remove binding for this variable.
      {b careful} if other bindings depend on this variable's binding... *)

  val deref_rec : subst:('ty, 'ty var) t -> 'ty var -> 'ty var
  (** For renamings, follow the substitution until we find an unbound var *)

  val find_deref_rec : subst:('ty, 'ty var) t -> 'ty var -> 'ty var option
  (** [find_deref_rec ~subst v] returns [Some (deref_rec subst v')] if [v]
      is bound, or [None] otherwise *)

  val rename_var : ('a, 'a var) t -> 'a var -> ('a, 'a var) t * 'a var
  (** [rename_var subst v] returns [subst', v'] where [v'] is
      a fresh copy of [v], and [subst' = add v v' subst] *)

  val mem : subst:('ty,'a) t -> 'ty var -> bool
  val find : subst:('ty,'a) t -> 'ty var -> 'a option
  val find_exn : subst:('ty,'a) t -> 'ty var -> 'a  (** @raise Not_found if var not bound *)
  val find_or : subst:('ty,'a) t -> default:'a -> 'ty var -> 'a

  val map : f:('a -> 'b) -> ('ty,'a) t -> ('ty,'b) t

  val to_list : ('ty,'a) t -> ('ty var * 'a) list

  val print : 'a CCFormat.printer -> (_, 'a) t CCFormat.printer
end

(** {2 Data structures} *)

module Set(Ty : sig type t end) : CCSet.S with type elt = Ty.t t


