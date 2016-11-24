
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Recursive Traversal of AST} *)

module type ARG = sig
  type t
  val equal : t -> t -> bool
  val hash : t -> int

  val print : t CCFormat.printer
  val section : Utils.Section.t
  val fail : ('a, Format.formatter, unit, 'b) format4 -> 'a
end

module Make(T : TermInner.S)(Arg : ARG)(State : sig type t end) : sig
  type term = T.t
  type ty = T.t

  type t
  (** A stateful object used for traversing a problem, eventually
      building a new list of statements *)

  type dispatch = {
    do_term:
      (t -> depth:int -> term -> term);

    do_goal_or_axiom :
      (t -> depth:int -> [`Goal | `Axiom] -> term -> term) option;

    do_def:
      (t -> depth:int ->
       (term, ty) Statement.rec_def ->
       Arg.t ->
       (term, ty) Statement.rec_def);

    do_pred:
      (t -> depth:int ->
       [`Wf | `Not_wf] -> [`Pred | `Copred] ->
       (term, ty) Statement.pred_def -> Arg.t ->
       (term, ty) Statement.pred_def);

    do_copy:
      (t -> depth:int -> loc:Location.t option ->
       (term, ty) Statement.copy ->
       Arg.t ->
       (term, ty) Statement.copy)
        option;

    do_spec:
      (t -> depth:int -> loc:Location.t option ->
       ID.t ->
       (term, ty) Statement.spec_defs ->
       Arg.t ->
       (term, ty) Statement.spec_defs)
        option;

    do_data:
      (t ->
       depth:int -> [`Data | `Codata] ->
       term Statement.tydef ->
       Arg.t ->
       term Statement.tydef)
      option;

    do_ty_def:
      (t ->
       ?loc:Location.t ->
       ty Statement.defined ->
       Arg.t ->
       ty Statement.defined)
      option;
  }

  val create :
    ?size:int ->
    ?max_depth:int ->
    env:(term,ty) Env.t ->
    state:State.t ->
    dispatch:dispatch ->
    unit ->
    t
  (** create a new traversal object.
      @param env the environment in which symbols are defined
      @param dispatch how to deal with definitions of symbols.
        Fields that are not specified are dealt with generically *)

  val env : t -> (term, ty) Env.t

  val state : t -> State.t

  val has_processed : t -> ID.t -> Arg.t -> bool
  (** Has {!mark_processed} already been called with those arguments? *)

  val mark_processed : t -> ID.t -> Arg.t -> unit
  (** To be used by callbacks in {!dispatch} to indicate that some additional
      IDs have been processed (e.g. the conversion functions of copy types) *)

  val processed : t -> (ID.t * Arg.t) Sequence.t
  (** All processed pairs *)

  val call_dep : t -> depth:int -> ID.t -> Arg.t -> unit
  (** [call_dep t id arg] is to be called during term traversal (typically,
      in {!dispatch.do_term}) to indicate the will of traversing the
      pair [(id,arg)] *)

  exception CannotTraverse

  val traverse_stmt :
    ?after_env:((term, ty) Env.t -> unit) ->
    t ->
    (term, ty) Statement.t ->
    unit
  (** Traverse the given statement, adding its translation to the result,
      updating the environment, etc.
      @raise CannotTraverse if {!get_statements} was called already
      @param after_env called once the environment is updated, but
      before the statment is actually traversed *)

  val get_statements: t -> (term, ty) Statement.t CCVector.vector
  (** [get_statements t] sorts topologically and merges the pieces of statements
      previously added by {!push_rec}, {!push_pred}, etc. and
      returns a valid list of statements.
      Once {!get_statements} has been called, {!traverse_stmt} will
      raise *)

  val max_depth_reached: t -> bool
end
