
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Scheduling of sub-processes}

  We need to run several instances of a solver in parallel, with distinct
  options. This module provides a clean interface to do that.
*)

type ('a, 'b) result =
  | Return of 'a
  | Return_shortcut of 'b  (** returns value, stop other processes *)
  | Fail of exn

val run :
  j:int ->
  cmd:('a -> string) ->
  f:(string -> in_channel * out_channel -> ('b, 'c) result) ->
  'a list ->
  ('b list, 'c) result
  (** [run ~j ~f ~cmd args] runs a subprocess for each element of [args],
    keeping at most [j] concurrent processes.
    For each [a] in [args], a subprocess is created with [cmd a],
    obtaining [stdout, stdin] that is given to [f] along with the command.
    Once [f] returns, its result influences the rest as follows:

    {ul
      {- if [f] returns [Return x], then [x] will be in the list of results
        iff every other process also returns [Return y] for some [y]}
      {- if [f] returns [Return_shortcut x], then still running processes
        are killed and [Return_shortcut x] is returned by the function}
      {- if [f] returns [Fail e], then still running processes are killed
        and [Fail e] is returned}
    }

    if [cmd] raises an exception [e], the whole functions returns [Fail e]
*)



