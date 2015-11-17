
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Utils: reduction, unification, etc.} *)

module ID = NunID
module Var = NunVar
module Env = NunEnv
module Subst = Var.Subst
module DBEnv = NunDBEnv
module T = NunTermEval
module VarSet = T.VarSet

type def_or_decl =
  | Local_def of T.term lazy_t (* x := t, [t] not evaluated yet *)
  | Local_decl of T.ty (* x : ty *)

(* a "toplevel" term, where [head] is not an application *)
type term_top = {
  head: T.term;
  env: def_or_decl DBEnv.t; (* variables declared or defined *)
  blocked: VarSet.t;
    (* the meta-variable to refine if we want to continue evaluating *)
}

(* compute the weak-head normal form *)
let rec whnf
: term_top -> term_top
= fun t ->


