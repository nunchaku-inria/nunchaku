
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Utils} *)

type 'a sequence = ('a -> unit) -> unit
type 'a or_error = ('a, string) CCResult.t

(** {2 Time} *)

module Time : sig
  val total : unit -> float
  (** time elapsed since start of program *)

  val start : unit -> float
  (** time at which the program started *)

  type timer
  (** A single-use timer, measures elapsed time  between {!start_timer()}
      and first call to {!stop_timer} *)

  val start_timer: unit -> timer

  val stop_timer : timer -> unit
  (** Stop timer, or does nothing if stopped already *)

  val get_timer : timer -> float
  (** Number of seconds elapsed between {!start_timer} and now, or
      between {!start_timer} and {!stop_timer} *)
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

val debugf : ?lock:bool -> ?section:Section.t -> int ->
  ('a, Format.formatter, unit, unit) format4 -> ('a -> unit) -> unit
(** Print a debug message, with the given section and verbosity level.
    The message might be dropped if its level is too high. *)

val debug : ?lock:bool -> ?section:Section.t -> int -> string -> unit

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

val fold_mapi : f:(int -> 'b -> 'a -> 'b * 'c) -> x:'b -> 'a list -> 'b * 'c list

val filteri : (int -> 'a -> bool) -> 'a list -> 'a list

val singleton_if : bool -> f:('a -> 'b) -> 'a -> 'b list

(** {2 Arg}
    Small overlay on top of {!Arg} *)

val arg_choice : (string * 'a) list -> ('a -> unit) -> Arg.spec
(** [arg_choice ~kind l f] picks a CLI option among the string in [l],
    and apply [f] to the result. *)

(** {2 Options} *)

(** Some global options that can also be changed on the CLI *)

module Options : sig
  val get_all : unit -> (Arg.key * Arg.spec * Arg.doc) list
  (** List of all options added so far *)

  val add : Arg.key * Arg.spec * Arg.doc -> unit
  (** Add an option to {!options_others_} *)

  val add_list : (Arg.key * Arg.spec * Arg.doc) list -> unit
  (** Add an option to {!options_others_} *)
end

(** {2 Warnings} *)

type warning =
  | Warn_overlapping_match
  | Warn_model_parsing_error

val toggle_warning : warning -> bool -> unit
(** Enable/disable the given warning *)

val is_warning_enabled : warning -> bool
(** Is this warning enabled? *)

val warning : warning -> string -> unit
(** Emit the given warning with the associated message *)

val warningf : warning -> ('a, Format.formatter, unit, unit) format4 -> 'a

(** {2 Misc} *)

exception NotImplemented of string

val pp_seq : ?sep:string -> 'a CCFormat.printer -> 'a Sequence.t CCFormat.printer
val pp_list : ?sep:string -> 'a CCFormat.printer -> 'a list CCFormat.printer

val pp_error_prefix : unit CCFormat.printer

val err_sprintf : ('a, Format.formatter, unit, string) format4 -> 'a

val not_implemented: string -> 'a
(** Raise an exception saying the given feature is not implemented *)

val not_implementedf: ('a, Format.formatter, unit, 'b) format4 -> 'a
(** Format-based version of {!not_implemented} *)

val failwithf : ('a, Format.formatter, unit, 'b) format4 -> 'a
(** Format version of {!failwith} *)

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
