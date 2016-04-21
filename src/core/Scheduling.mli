
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Scheduling of sub-processes}

  We need to run several instances of a solver in parallel, with distinct
  options. This module provides a clean interface to do that.
*)

(** {2 MVar}

    A MVar is a value that is only accessed atomically *)

module MVar : sig
  type 'a t
  val make : 'a -> 'a t
  val get : 'a t -> 'a
  val set : 'a t -> 'a -> unit
  val update : f:('a -> 'a * 'b) -> 'a t -> 'b
end

(** {2 Futures}

    A future runs in a newly created thread. *)

module Fut : sig
  type 'a t

  val return : 'a -> 'a t

  type 'a final_state =
    | Stopped
    | Done of 'a
    | Fail of exn

  val make :
    ?on_res:('a final_state -> unit) list ->
    (unit -> 'a) ->
    'a t

  val stop : _ t -> unit

  val is_done : _ t -> bool

  val on_res : 'a t -> f:('a final_state -> unit) -> unit

  val get : 'a t -> 'a final_state
end

(** {2 Invoke sub-process}

    The subprocess is managed in a thread, hidden behind a future.
    Cancelling the future will kill the subprocess *)

val popen :
  ?on_res:('a Fut.final_state -> unit) list ->
  string ->
  f:(out_channel * in_channel -> 'a) ->
  'a Fut.t
(** [popen cmd ~f] starts a subprocess executing [cmd], and calls
    [f] with the [(stdin,stdout)] of the sub-process, in a new thread.
    @return the future result of [f] *)

(** {2 Task} *)

type shortcut =
  | Shortcut
  | No_shortcut

module Task : sig
  type 'res t
  (** Task returning a value of type ['res] when executed *)

  val make :
    ?prio:int ->
    (unit -> 'a * shortcut) ->
    'a t
  (** [make f] creates a new task that will execute [f] in a separate thread.
      @param prio the priority (default 50); the lower, the more important
      @param post post-processing of the value *)

  val of_fut :
    ?prio:int ->
    (unit -> ('a * shortcut) Fut.t) ->
    'a t
  (** [of_fut f] is similar to {!make}, but [f] produces a future, not a direct
      result *)

  val map : f:('a -> 'b) -> 'a t -> 'b t
  (** Map the result *)
end

type 'a run_result =
  | Res_one of 'a
  | Res_list of 'a list
  | Res_fail of exn

val run :
  j:int ->
  'res Task.t list ->
  'res run_result
(** [run ~j tasks] runs the given list of tasks in at most [j] simultaneous
    threads, possibly exiting early if a task returns {!Return_shortcut}.

    For a task [t]:
    {ul
      {- if [t] returns [Return x], then [x] will be in the list of results
        iff every other process also returns [Return y] for some [y]}
      {- if [t] returns [Return_shortcut x], then still running processes
        are killed and [Return_shortcut x] is returned by the function}
      {- if [t] returns [Fail e], then still running processes are killed
        and [Fail e] is returned}
    }

    If some task [t] raises an exception [e],
    the whole functions returns [Fail e].
*)
