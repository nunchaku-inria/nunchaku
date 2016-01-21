(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Model} *)

type 'a printer = Format.formatter -> 'a -> unit

(** {2 Decision Trees}

    A decision tree is a nested if/then/else used to describe functions
    over finite domains. *)

module DT : sig
  type ('t, 'ty) test = 'ty Var.t * 't (** Equation var=term *)

  val print_test : 't CCFormat.printer -> ('t, _) test CCFormat.printer
  val print_tests : 't CCFormat.printer -> ('t, _) test list CCFormat.printer

  type (+'t, +'ty) t = private {
    tests: (('t, 'ty) test list * 't) list;
      (* [(else) if v_1 = t_1 & ... & v_n = t_n then ...] *)

    else_ : 't;
      (* else t *)
  }

  val yield : 't -> ('t, 'ty) t
  val ite : ('ty Var.t * 't) list -> 't -> ('t, 'ty) t -> ('t, 'ty) t
  val test : (('t, 'ty) test list * 't) list -> else_:'t -> ('t, 'ty) t
  val test_flatten : (('t,'ty) test list * 't) list -> else_:('t,'ty) t -> ('t,'ty) t

  val map :
    ?var:('ty1 Var.t -> 'ty2 Var.t option) ->
    term:('t1 -> 't2) ->
    ty:('ty1 -> 'ty2) ->
    ('t1,'ty1) t ->
    ('t2,'ty2) t

  val print : 't printer -> ('t,_) t printer
end

type ('t,'ty) decision_tree = ('t,'ty) DT.t

(** {2 Helpers for Decision Trees} *)

module DT_util(T : TermInner.S) : sig
  val eval : subst:(T.t,T.t) Var.Subst.t -> (T.t, T.t) DT.t -> T.t
  (** Evaluate a decision tree on the given substitution.
      @raise Not_found if some variable in [dt.vars] is not bound. *)

  val to_term : (T.t, T.t) DT.t -> T.t
  (** Convert the decision tree to a term *)
end

(** {2 Models} *)

type (+'t, +'ty) t = {
  constants: ('t * 't) list;
    (* constant -> its interpretation *)

  funs: ('t * 'ty Var.t list * ('t,'ty) decision_tree) list;
    (* fun * var list -> body *)

  finite_types: ('ty * ID.t list) list;
    (* type -> finite domain *)

  potentially_spurious: bool;
    (** the model might be spurious, i.e. some approximation made the
        translation unsound *)
}

val empty : (_,_) t
(** Empty model *)

val add_const : ('t,'ty) t -> 't * 't -> ('t,'ty) t
(** Add a term interpretation *)

val add_fun : ('t,'ty) t -> 't * 'ty Var.t list * ('t,'ty) decision_tree -> ('t,'ty) t
(** Add a function interpretation *)

val add_finite_type : ('t, 'ty) t -> 'ty -> ID.t list -> ('t, 'ty) t
(** Map the type to its finite domain. *)

val fold :
  constants:('acc -> 'a * 'a -> 'acc) ->
  funs:('acc -> 'a * 'b Var.t list * ('a,'b) decision_tree -> 'acc) ->
  finite_types:('acc -> 'b * ID.t list -> 'acc) ->
  'acc ->
  ('a,'b) t ->
  'acc

val iter :
  constants:('a * 'a -> unit) ->
  funs:('a * 'b Var.t list * ('a,'b) decision_tree -> unit) ->
  finite_types:('b * ID.t list -> unit) ->
  ('a,'b) t ->
  unit

val filter_map :
  constants:('t1 * 't1 -> ('t2 * 't2) option) ->
  funs:('t1 * 'ty1 Var.t list * ('t1,'ty1) decision_tree ->
         ('t2 * 'ty2 Var.t list * ('t2,'ty2) decision_tree) option) ->
  finite_types:('ty1 * ID.t list -> ('ty2 * ID.t list) option) ->
  ('t1, 'ty1) t ->
  ('t2, 'ty2) t

val map :
  term:('t1 -> 't2) ->
  ty:('ty1 -> 'ty2) ->
  ('t1, 'ty1) t ->
  ('t2, 'ty2) t

val print : 't printer -> 'ty printer -> ('t,'ty) t printer

module Util(T : TermInner.S) : sig
  val rename : (T.t, T.t) t -> (T.t, T.t) t
  (** [rename m] performs a renaming of domain constants and bound variables
      that should be regular and readable.
      Assumes the types that have finite domains are ground types.
      @raise Invalid_argument if some assumption is invalidated *)

  val pipe_rename :
    print:bool ->
    ('a, 'a, (T.t, T.t) t, (T.t, T.t) t) Transform.t
end
