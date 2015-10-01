
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Location in a file} *)

(** {2 Location} *)

type t = {
  file : string;
  start_line : int;
  start_column : int;
  stop_line : int;
  stop_column : int;
}

val mk : string -> int -> int -> int -> int -> t

val mk_pair : string -> (int * int) -> (int * int) -> t

val mk_pos : Lexing.position -> Lexing.position -> t
(** Use the two positions of lexbufs. The file of the first lexbuf is used *)

include NunIntf.EQ with type t := t
include NunIntf.HASH with type t := t

val combine : t -> t -> t
(** Position that spans the two given positions. The file is assumed to be
    the same in both case, and is chosen from one of the two positions. *)

val combine_list : t list -> t
(** N-ary version of {!combine}.
    @raise Invalid_argument if the list is empty *)

val smaller : t -> than:t -> bool
(** [smaller p ~than] is true if [p] is included in [than], ie
    [p] is a sub-location of [than] (interval inclusion) *)

include NunIntf.PRINT with type t := t

val to_string : t -> string

val print_opt : Format.formatter -> t option -> unit

val to_string_opt : t option -> string

(** {2 Value bundled with Location} *)

type 'a with_loc = {
  loc: t option;
  value: 'a;
}

val with_loc: ?loc:t -> 'a -> 'a with_loc
(** [with_loc ?loc x] makes a value with the given location *)

val get : 'a with_loc -> 'a
val get_loc : _ with_loc -> t option

(** {2 Lexbuf}

  Utils to set/get the file in a lexbuf *)

val set_file : Lexing.lexbuf -> string -> unit
(** Change the file name used for positions in this lexbuf *)

val of_lexbuf : Lexing.lexbuf -> t
(** Recover a position from a lexbuf *)
