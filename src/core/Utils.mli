
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Utils} *)

type 'a sequence = ('a -> unit) -> unit
type 'a or_error = [`Ok of 'a | `Error of string]

(** {2 Time} *)

module Time : sig
  val total : unit -> float
  (** time elapsed since start of program *)

  val start : unit -> float
  (** time at which the program started *)
end

(** {2 Debugging} *)

(** Debug section *)
module Section : sig
  type t

  val full_name : t -> string  (** Full path to the section *)

  val set_debug : t -> int -> unit
  (** Debug level for section (and its descendants) *)

  val clear_debug : t -> unit
  (** Clear debug level (will be same as parent's) *)

  val get_debug : t -> int option
  (** Specific level of this section, if any *)

  val cur_level : t -> int
  (** Current debug level, with parent inheritance *)

  val iter : (string * t) sequence
  (** all registered sections *)

  val root : t
  (** Default section, with no parent *)

  val make : ?parent:t -> ?inheriting:t list -> string -> t
  (** [make ?parent ?inheriting name] makes a new section with the given name.
      It has a parent (default [root]), used to give it a name. It can
      also have a list of sections it inherits from.
      Unless specificed explicitely otherwise (using
      {!set_debug}, the level of the section will be the max level of its
      parent and its inherited sections. *)
end

val set_debug : int -> unit     (** Set debug level of [Section.root] *)
val get_debug : unit -> int     (** Current debug level for [Section.root] *)

val debugf : ?section:Section.t -> int ->
            ('a, Format.formatter, unit, unit) format4 -> ('a -> unit) -> unit
(** Print a debug message, with the given section and verbosity level.
    The message might be dropped if its level is too high. *)

val debug : ?section:Section.t -> int -> string -> unit

(** {2 Callbacks} *)

module Callback : sig
  type 'a t
  (** Set of callbacks where callbacks have type ['a] *)

  type callback_id = private int
  (** The unique identifier of a given callback (for removal) *)

  val create : unit -> 'a t

  val register : 'a t -> f:'a -> callback_id
  (** Register a new callback *)

  val remove : _ t -> id:int -> unit
  (** Remove the callback with given ID *)

  val iter : 'a t -> f:('a -> unit) -> unit
  (** Iterate on callbacks *)

  val call1 : ('a -> unit) t -> 'a -> unit
  (** [call1 l x] is short for [iter l ~f:(fun f -> f x)] *)

  val call2 : ('a -> 'b -> unit) t -> 'a -> 'b -> unit
  (** [call2 l x y] is short for [iter l ~f:(fun f -> f x y)] *)
end

(** {2 Vector} *)

val vec_fold_map :  ('b -> 'a -> 'b * 'c) -> 'b -> ('a,_) CCVector.t -> 'b * ('c,[`RW]) CCVector.t

(** {2 Lists} *)

val fold_map : ('b -> 'a -> 'b * 'c) -> 'b -> 'a list -> 'b * 'c list

val fold_mapi : (int -> 'b -> 'a -> 'b * 'c) -> 'b -> 'a list -> 'b * 'c list

val singleton_if : bool -> f:('a -> 'b) -> 'a -> 'b list

(** {2 Warnings} *)

type warning =
  | Warn_overlapping_match

val toggle_warning : warning -> bool -> unit
(** Enable/disable the given warning *)

val is_warning_enabled : warning -> bool
(** Is this warning enabled? *)

val warning : warning -> string -> unit
(** Emit the given warning with the associated message *)

val warningf : warning -> ('a, Format.formatter, unit, unit) format4 -> 'a

val options_warnings_ : (Arg.key * Arg.spec * Arg.doc) list

(** {2 Misc} *)

exception NotImplemented of string

val pp_error_prefix : unit CCFormat.printer

val err_sprintf : ('a, Format.formatter, unit, string) format4 -> 'a

val not_implemented: string -> 'a
(** Raise an exception saying the given feature is not implemented *)

val not_implementedf: ('a, Format.formatter, unit, 'b) format4 -> 'a
(** Format-based version of {!not_implemented} *)

val err_of_exn: exn -> _ or_error
(** Make an error out of an exception, with the stack trace *)

val exn_ksprintf :
  f:(string -> exn) ->
  ('a, Format.formatter, unit, 'b) format4 ->
  'a
(** A sprintf implementation for formatters, that calls an exception
    raising function [f] *)


val ignore_catch : ('a -> 'b) -> 'a -> unit
(** [ignore_catch f x] computes [f x], ignores the result, and also
    ignores any exception raised by [f x]. *)
