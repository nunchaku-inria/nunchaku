
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Simple and efficient S-expression parsing/printing}

    Windows-aware printer and parser, using ocamllex/ocamlyacc *)

type 'a or_error = [ `Ok of 'a | `Error of string ]
type 'a sequence = ('a -> unit) -> unit
type 'a gen = unit -> 'a option

type t = [
  | `Atom of string
  | `List of t list
]
type sexp = t

val atom : string -> t
val list : t list -> t

val pp : t CCFormat.printer
(** Pretty-printer nice on human eyes (including indentation) *)

val to_string : t -> string

val to_chan : out_channel -> t -> unit

val to_file : string -> t -> unit

type 'a parse_result = ['a or_error | `End ]
(** A parser of ['a] can return [`Ok x] when it parsed a value,
    or [`Error e] when a parse error was encountered, or
    [`End] if the input was empty *)

module Decoder : sig
  type t
  (** Decoder *)

  val of_lexbuf : Lexing.lexbuf -> t

  val next : t -> sexp parse_result
  (** Parse the next S-expression or return an error if the input isn't
      long enough or isn't a proper S-expression *)
end

val parse_string : string -> t or_error
(** Parse a string *)

val parse_chan : in_channel -> t or_error
(** Parse a S-expression from the given channel. Can read more data than
    necessary, so don't use this if you need finer-grained control (e.g.
    to read something else {b after} the S-exp) *)

val parse_chan_list : in_channel -> t list or_error

val parse_file : string -> t or_error
(** Open the file and read a S-exp from it *)

val parse_file_list : string -> t list or_error
(** Open the file and read a S-exp from it *)
