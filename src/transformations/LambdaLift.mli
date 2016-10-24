
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Lambda Lifting}

    Remaining λ expressions are extracted as toplevel {b named} functions;
    equalities such as [(fun x. t) = (fun y. u)] are replaced by
    [forall x. t = u[x/y]]. *)

open Nunchaku

type term = TermInner.Default.t

val name : string

type state

val tr_problem :
  (term, term) Problem.t ->
  (term, term) Problem.t * state

val decode_model :
  state:state -> (term,term) Model.t -> (term,term) Model.t

val pipe :
  print:bool ->
  check:bool ->
  ((term,term) Problem.t,
    (term,term) Problem.t,
    (term,term) Problem.Res.t, (term,term) Problem.Res.t
  ) Transform.t

(** Similar to {!pipe} but with a generic decode function.
    @param print if true, prints problem after lifting
    @param check if true, check the invariants on the result *)
val pipe_with :
  decode:(state -> 'c -> 'd) ->
  print:bool ->
  check:bool ->
  ((term,term) Problem.t,
    (term,term) Problem.t, 'c, 'd
  ) Transform.t
