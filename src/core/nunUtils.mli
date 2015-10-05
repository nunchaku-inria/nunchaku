
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
            ('a, Format.formatter, unit, unit) format4 -> 'a
(** Print a debug message, with the given section and verbosity level.
    The message might be dropped if its level is too high. *)

(** {2 Misc} *)

exception NotImplemented of string

val not_implemented: string -> 'a
(** Raise an exception saying the given feature is not implemented *)

val err_of_exn: exn -> _ or_error
(** Make an error out of an exception, with the stack trace *)

