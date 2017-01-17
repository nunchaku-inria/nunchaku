(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Model} *)

type 'a printer = Format.formatter -> 'a -> unit
type 'a prec_printer = Precedence.t -> 'a printer
type 'a to_sexp = 'a -> Sexp_lib.t

(** {2 Decision Trees}

    A decision tree is a nested if/then/else used to describe functions
    over finite domains. *)

module DT : sig
  (* a decision tree *)
  type (+'t, +'ty) t = private
    | Yield of 't
    | Cases of ('t, 'ty) cases

  (* a nested if/then/else on a given variable *)
  and (+'t, +'ty) cases = {
    var: 'ty Var.t;
    (* the variable being tested *)
    tests: ('t, 'ty) case list;
    (* list of [if var=term, then sub-dt] *)
    default: ('t, 'ty) t option;
    (* sub-dt by default *)
  }

  and ('t, 'ty) case = 't * ('t, 'ty) t

  val yield : 't -> ('t, _) t
  (** DT on 0 variables, that returns its argument *)

  val const : 'ty Var.t list -> ('t,'ty) t -> ('t,'ty) t
  (** [const vars ret] is the constant function over [vars], that
      always return [ret] *)

  val cases :
    'ty Var.t ->
    tests:('t, 'ty) case list ->
    default:('t, 'ty) t option ->
    ('t, 'ty) t
  (** @raise Invalid_argument if [tests= [] && default = None] *)

  val map :
    term:('t1 -> 't2) ->
    ty:('ty1 -> 'ty2) ->
    ('t1,'ty1) t ->
    ('t2,'ty2) t

  val filter_map :
    test:('ty Var.t -> 't1 -> 't2 option) ->
    yield:('t1 -> 't2) ->
    ('t1,'ty) t ->
    ('t2,'ty) t
  (** [filter_map ~test ~yield dt] filters the branches of [dt]
      using [test v lhs] on every test [v=lhs], and maps the
      leaves using [yield] *)

  val ty_args : (_, 'ty) t -> 'ty list
  (** Type of the discrimination tree arguments, seen as a function *)

  val vars : (_, 'ty) t -> 'ty Var.t list
  (** List of variables decided upon *)

  val num_vars : (_,_) t -> int

  val add_default : 't -> ('t, 'ty) t -> ('t, 'ty) t
  (** [add_default term dt] adds [term] as a default case for every
      sub-case of [dt] that does not already have a default value *)

  (** A test for the flat model *)
  type ('t, 'ty) flat_test = {
    ft_var: 'ty Var.t;
    ft_term: 't;
  }

  (** A flat model *)
  type ('t, 'ty) flat_dt = {
    fdt_vars: 'ty Var.t list;
    fdt_cases: (('t, 'ty) flat_test list * 't) list;
    fdt_default: 't option;
  }

  val mk_flat_test : 'ty Var.t -> 't -> ('t, 'ty) flat_test

  val of_flat :
    equal:('t -> 't -> bool) ->
    hash:('t -> int) ->
    ('t, 'ty) flat_dt ->
    ('t, 'ty) t
  (** [of_flat vars ~tests ~default ] builds a  decision tree on [vars], in
      that order, asssuming [tests] only range over [vars].
      @param eq equality on terms *)

  val flatten :
    ('t, 'ty) t ->
    ('t, 'ty) flat_dt
  (** Flatten as an old style flat decision tree *)

  val check_ : (_,_) t -> unit
  (** check some invariants *)

  val print : 't prec_printer -> 'ty printer -> ('t, 'ty) t printer

  val print_flat_test : 't prec_printer -> ('t, _) flat_test printer
  val print_flat : 't prec_printer -> ('t, _) flat_dt printer

  val to_sexp : 't to_sexp -> 'ty to_sexp ->('t, 'ty) t to_sexp
  (** for model display *)
end

(** {2 Helpers for Decision Trees} *)

module DT_util : sig
  type term = TermInner.Default.t

  type dt = (term, term) DT.t
  type subst = (term, term) Var.Subst.t

  val ite : term Var.t -> then_: dt -> else_: dt -> dt

  val eval_subst : subst:subst -> dt -> dt
  (** Eval the tree with the given substitution (which does not capture
      the tree's variables)
      @raise Assert_failure if the substitution binds some of [dt]'s variables *)

  val map_vars : subst:(term, term Var.t) Var.Subst.t -> dt -> dt
  (** Apply the substitution to the tree's variables and terms *)

  val rename_vars : dt -> dt
  (** Rename all variables in [dt] *)

  val apply : dt -> term -> dt
  (** [apply dt arg] returns the sub-tree of [dt] for when [dt]'s variable
      is equal to [arg].
      @raise Invalid_argument if the [dt] is not a function *)

  val apply_l : dt -> term list -> dt
  (** apply the [dt] to a list of arguments
      @raise Invalid_argument if the [dt] is not a function with enough arguments *)

  val join : dt -> dt -> dt
  (** [join a b] applies [b] to every leaf of [a], grafting the
      resulting sub-tree in place of the leaf, using {!apply}.

      assumes the return type of [a] is the same as the first
      argument of [b]. *)

  val merge : dt -> dt -> dt
  (** [merge a b] concatenates the cases of [a] and [b],
      merging the common cases recursively, favoring [a] over [b]
      when needed. The new default/else is [a.default].

      not commutative. *)

  val merge_l : dt list -> dt
  (** n-ary version of {!merge}
      @raise Invalid_argument if the list is empty *)

  val reorder : term Var.t list -> dt -> dt
  (** [reorder vars dt] rebalances [dt] so it has the given order of
      variables. It is assumed that [vars] is a permutation of [DT.vars dt]
      @raise Invalid_argument if [vars] is not a permutation of the
        variables of [dt] *)

  val remove_vars : term Var.t list -> dt -> dt
  (** Remove the given variables, using {!merge_l} to merge their sub-cases.
      If those variables occur in tests in variables that come earlier
      in [DT.vars dt], they will not be substituted properly *)

  val remove_first_var : dt -> dt
  (** remove the first variable, using {!remove_vars}.
      @raise Invalid_argument if the tree is constant *)

  exception Case_not_found of term

  val find_cases : ?subst:subst -> term -> (term, term) DT.cases -> subst * dt
  (** @raise Case_not_found if the term is not found *)

  val to_term : dt -> term
  (** Convert the decision tree to a term *)

  val print : dt printer
end

(** {2 Models} *)

type symbol_kind =
  | Symbol_prop
  | Symbol_fun
  | Symbol_utype
  | Symbol_data
  | Symbol_codata

type (+'t, +'ty) value_def = 't * ('t, 'ty) DT.t * symbol_kind

(** A model *)
type (+'t, +'ty) t = {
  values: ('t, 'ty) value_def list;
  (* term -> its interpretation *)

  finite_types: ('ty * ID.t list) list;
  (* type -> finite domain *)

  potentially_spurious: bool;
  (** the model might be spurious, i.e. some approximation made the
        translation unsound *)
}

type ('a,'b) model = ('a,'b) t

val empty : (_,_) t
(** Empty model *)

val empty_copy : ('t, 'ty) t -> ('t, 'ty) t
(** [empty_copy m] is a empty model that has the same additional information
    (such as {!potentially_spurious}) as [m] *)

val add_const : ('t,'ty) t -> 't * 't * symbol_kind -> ('t,'ty) t
(** Add a constant term interpretation *)

val add_value : ('t,'ty) t -> 't * ('t, 'ty) DT.t * symbol_kind -> ('t,'ty) t
(** Add a value interpretation *)

val add_finite_type : ('t, 'ty) t -> 'ty -> ID.t list -> ('t, 'ty) t
(** Map the type to its finite domain. *)

val values : ('t, 'ty) t -> ('t * ('t, 'ty) DT.t * symbol_kind) Sequence.t
val finite_types : (_, 'ty) t -> ('ty * ID.t list) Sequence.t

val fold :
  ?values:('acc -> 'a * ('a, 'b) DT.t * symbol_kind -> 'acc) ->
  ?finite_types:('acc -> 'b * ID.t list -> 'acc) ->
  'acc ->
  ('a,'b) t ->
  'acc

val iter :
  ?values:('a * ('a, 'b) DT.t * symbol_kind -> unit) ->
  ?finite_types:('b * ID.t list -> unit) ->
  ('a,'b) t ->
  unit

val filter_map :
  values:('t1 * ('t1, 'ty1) DT.t * symbol_kind ->
    ('t2 * ('t2, 'ty2) DT.t * symbol_kind) option) ->
  finite_types:('ty1 * ID.t list -> ('ty2 * ID.t list) option) ->
  ('t1, 'ty1) t ->
  ('t2, 'ty2) t

val map :
  term:('t1 -> 't2) ->
  ty:('ty1 -> 'ty2) ->
  ('t1, 'ty1) t ->
  ('t2, 'ty2) t

val filter :
  ?values:('t * ('t, 'ty) DT.t * symbol_kind -> bool) ->
  ?finite_types:('ty * ID.t list -> bool) ->
  ('t, 'ty) t ->
  ('t, 'ty) t

val print : 't prec_printer -> 'ty printer -> ('t,'ty) t printer
(** Debug printing *)

val to_sexp : 't to_sexp -> 'ty to_sexp -> ('t,'ty) t to_sexp
(** S-expr output suitable for parsing from the caller *)

module Default : sig
  type term = TermInner.Default.t

  type t = (term, term) model

  val to_sexp : t to_sexp

  val print_standard : t printer
  (** Printer suitable for parsing from the caller *)
end
