
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Top-Level Statements (with locations)} *)

type loc = NunLocation.t
type id = NunID.t
type 'a printer = Format.formatter -> 'a -> unit
type 'a or_error = [`Ok of 'a | `Error of string]

(** {2 Top-level statement} *)

module Statement : sig
  type decl =
    | Decl_type
    | Decl_fun
    | Decl_prop

  (** defines [t], aliased as local variable [v], with the [axioms].
    All the type variables [alpha_1, ..., alpha_n] are free in [t]
    and in [axioms], and no other type variable should occur. *)
  type ('t,'ty) case = {
    case_vars: 'ty NunVar.t list; (* alpha_1, ..., alpha_n *)
    case_defined: 't; (* t *)
    case_alias: 'ty NunVar.t; (* v *)
    case_axioms: 't list; (* axioms *)
  }

  val case_vars : ('t,'ty) case -> 'ty NunVar.t list
  val case_alias : ('t,'ty) case -> 'ty NunVar.t
  val case_defined : ('t,'ty) case -> 't
  val case_axioms : ('t,'ty) case -> 't list

  (** mutual definition of several terms *)
  type ('t,'ty) mutual_cases = ('t,'ty) case list

  (* TODO: selectors? *)

  (** A type constructor: name + type of arguments *)
  type 'ty ty_constructor = {
    cstor_name: id; (** Name *)
    cstor_args: 'ty list; (** type arguments *)
    cstor_type: 'ty; (** type of the constructor (shortcut) *)
  }

  (** A (co)inductive type. The type variables [ty_vars] occur freely in
      the constructors' types. *)
  type 'ty tydef = {
    ty_id : id;
    ty_vars : 'ty NunVar.t list;
    ty_type : 'ty; (** shortcut for [type -> type -> ... -> type] *)
    ty_cstors : 'ty ty_constructor list;
  }

  val tydef_vars : 'ty tydef -> 'ty NunVar.t list
  val tydef_id : _ tydef -> id
  val tydef_type : 'ty tydef -> 'ty
  val tydef_cstors : 'ty tydef -> 'ty ty_constructor list

  (** Mutual definitions of several types *)
  type 'ty mutual_types = 'ty tydef list

  (** Flavour of axiom *)
  type ('t,'ty) axiom =
    | Axiom_std of 't list
      (** Axiom list that can influence consistency (no assumptions) *)
    | Axiom_spec of ('t,'ty) mutual_cases
      (** Axioms can be safely ignored, they are consistent *)
    | Axiom_rec of ('t,'ty) mutual_cases
      (** Axioms are part of an admissible (partial) definition *)

  type ('term, 'ty) view =
    | Decl of id * decl * 'ty
    | Axiom of ('term, 'ty) axiom
    | TyDef of [`Data | `Codata] * 'ty mutual_types
    | Goal of 'term

  (** Additional informations on the statement *)
  type info = {
    loc: loc option;
    name: string option;
  }

  val info_default : info

  type ('term, 'ty) t = private {
    view: ('term, 'ty) view;
    info: info;
  }

  val view : ('term,'ty) t -> ('term, 'ty) view
  val loc : (_,_) t -> loc option
  val name : (_,_) t -> string option
  val info : (_,_) t -> info

  val mk_decl : info:info  -> id -> decl -> 'ty -> ('t,'ty) t
  val mk_axiom : info:info -> ('a,'ty) axiom -> ('a, 'ty) t
  val mk_ty_def : info:info -> [`Data | `Codata] -> 'ty mutual_types -> (_, 'ty) t

  val ty_decl : info:info -> id -> 'a -> (_, 'a) t
  (** declare a type constructor *)

  val decl : info:info -> id -> 'a -> (_, 'a) t
  (** declare a function symbol *)

  val prop_decl : info:info -> id -> 'a -> (_, 'a) t
  (** Declare a proposition ([prop] must be provided) *)

  val axiom : info:info -> 'a list -> ('a,_) t
  (** Axioms without additional assumptions *)

  val axiom1 : info:info -> 'a -> ('a,_) t

  val axiom_spec : info:info -> ('a,'ty) mutual_cases -> ('a,'ty) t
  (** Axiom that can be ignored if not explicitely depended upon by the goal *)

  val axiom_rec : info:info -> ('a,'ty) mutual_cases -> ('a,'ty) t
  (** Axiom that is part of an admissible (mutual, partial) definition. *)

  val data : info:info -> 'ty mutual_types -> (_, 'ty) t

  val codata : info:info -> 'ty mutual_types -> (_, 'ty) t

  val goal : info:info -> 'a -> ('a,_) t
  (** The goal of the problem *)

  val map_case :
    term:('t -> 't2) ->
    ty:('ty -> 'ty2) ->
    ('t, 'ty) case ->
    ('t2, 'ty2) case

  val map_cases :
    term:('t -> 't2) ->
    ty:('ty -> 'ty2) ->
    ('t, 'ty) mutual_cases ->
    ('t2, 'ty2) mutual_cases

  val map :
    term:('t -> 't2) ->
    ty:('ty -> 'ty2) ->
    ('t, 'ty) t ->
    ('t2, 'ty2) t

  val fold :
    term:('a -> 't -> 'a) ->
    ty:('a -> 'ty -> 'a) ->
    'a -> ('t, 'ty) t -> 'a

  (** {2 Print} *)

  val print : 'a printer -> 'b printer -> ('a,'b) t printer
  val print_list : 'a printer -> 'b printer -> ('a,'b) t list printer
end

(** {2 Signature} *)

module Signature : sig
  type 'ty t = 'ty NunID.Map.t

  val empty : _ t

  val mem : sigma:'a t -> id -> bool
  val find : sigma:'a t -> id -> 'a option
  val find_exn : sigma:'a t -> id -> 'a (** @raise Not_found if not present *)

  val declare : sigma:'a t -> id -> 'a -> 'a t
end

(** {2 Problem: a Set of Statements + Signature} *)

type ('t, 'ty) t = private {
  statements : ('t, 'ty) Statement.t list;
}

val make :
  ('t, 'ty) Statement.t list ->
  ('t, 'ty) t
(** Build a problem from a list of statements *)

val statements : ('t, 'ty) t -> ('t, 'ty) Statement.t list

val map : term:('a -> 'b) -> ty:('tya -> 'tyb) -> ('a, 'tya) t -> ('b, 'tyb) t

val map_with :
  ?before:(unit -> ('b, 'tyb) Statement.t list) ->
  ?after:(unit -> ('b, 'tyb) Statement.t list) ->
  term:('a -> 'b) ->
  ty:('tya -> 'tyb) ->
  ('a, 'tya) t -> ('b, 'tyb) t
(** [map_with ~add ~term ~ty pb] is similar to [map ~term ~ty pb], but after
    processing each statement [st], [after ()] and [before()] are called,
    and the statements they return
    are added respectively before or after the translation of [st]. *)

val print : 'a printer -> 'b printer -> ('a,'b) t printer
(** Printer for a problem *)

exception IllFormed of string
(** Ill-formed problem *)

val goal : ('t, _) t -> 't
(** [goal pb] returns the unique goal of [pb], or fails. A problem that doesn't
    have a single goal is ill-formed
    @raise IllFormed if the problem doesn't have exactly one goal *)

val signature : ?init:'ty Signature.t -> (_, 'ty) t -> 'ty Signature.t
(** Gather the signature of every declared symbol
    @param init initial signature, if any
    @raise IllFormed if some symbol is declared twice *)

(** {2 Model} *)

module Model : sig
  type 't t = ('t * 't) list

  val map : f:('a -> 'b) -> 'a t -> 'b t

  val print : 't printer -> 't t printer
end

(** {2 Result} *)

module Res : sig
  type 't t =
    | Unsat
    | Sat of 't Model.t
    | Timeout

  val map : f:('a -> 'b) -> 'a t -> 'b t

  val print : 't printer -> 't t printer
end
