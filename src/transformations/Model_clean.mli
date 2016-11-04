
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Cleanup models}

    - rename values to something more "canonical"
    - eliminate recursive definitions in decision trees *)

open Nunchaku_core

type term = TermInner.Default.t
type model = (term, term) Model.t

val name : string

val rename : model -> model
(** [rename m] performs a renaming of domain constants and bound variables
      that should be regular and readable.
      Assumes the types that have finite domains are ground types.
      @raise Invalid_argument if some assumption is invalidated *)

val remove_recursion : model -> model
(** [remove_recursion m] transforms definitions such as
      [f x = if x=0 then 0 else if x=1 then f 0 else ...]
    into [f x = if x=0 then 0 else if x=1 then 0 else ...] *)

val pipe :
  print:bool ->
  ('a, 'a, (term, term) Problem.Res.t, (term, term) Problem.Res.t) Transform.t
