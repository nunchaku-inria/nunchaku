
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Administrative Normal Form AST, for Narrowing} *)

module ID = NunID
module Var = NunVar
module Env = NunEnv
module Subst = Var.Subst

type id = ID.t
type 'a var = 'a Var.t
type 'a printer = Format.formatter -> 'a -> unit

let fpf = Format.fprintf

module Builtin : sig
  type t =
    [ `Eq
    ]
  val print : t printer
end = struct
  type t =
    [ `Eq
    ]
  let print out = function
    | `Eq -> fpf out "="
end

type 'a case = 'a var list * 'a
type 'a cases = 'a case ID.Map.t

(** A nested program, chaining computations. *)
type expr = {
  cell: expr_cell;
  blocked: value var option;
    (* the variable to refine if we want to continue evaluating *)
}
and expr_cell =
  | Val of value
  | Let of v_var * computation * expr (** Shallow let *)
  | Match of v_var * expr cases (** Shallow match *)
  | Ite of v_var * expr * expr (** Shallow if/then/else *)
  | Forall of v_var * expr (** Introduce a new rigid variable *)
  | Exists of v_var * expr (** Introduce a new meta *)
  | And of expr list
  | Or of expr list

(** A value in WHNF, not evaluable further except by refining metas *)
and value =
  | True
  | False
  | App of id * value list (** Constructor *)
  | HOApp of v_var * value list (** higher-order application of opaque var *)
  | Var of v_var (** Typically, opaque constant, like an existential *)
  | Meta of expr var (** Existential variable *)
  | Fun of v_var * expr (** Function *)

(** Variable bound to a value — never to an expression *)
and v_var = value var

(** A shallow computation *)
and computation =
  | C_app_var of v_var * value list (** [fun_var, args] *)
  | C_app_id of id * value list (** [fun_name, args] or constructor app *)
  | C_app_builtin of Builtin.t * value list
  | C_val of value (** Value, in which some variables might be substituted *)

(** A type *)
and ty =
  | TyApp of id * ty list
  | TyVar of ty var
  | TyForall of ty var * ty

(** {2 Utils} *)

let mk_expr_ ~blck e = {cell=e; blocked=blck;}

let mk_val v = mk_expr_ ~blck:None (Val v)
let mk_let ~blck v t u = mk_expr_ ~blck (Let (v,t,u))
let mk_match ~blck v l = mk_expr_ ~blck (Match (v,l))
let mk_ite ~blck a b c = mk_expr_ ~blck (Ite (a,b,c))

let v_true = True
let v_false = False
let v_app c l = App (c,l)
let v_ho_app f l = HOApp (f,l)
let v_var v = Var v
let v_meta v = Meta v
let v_fun v t = Fun (v,t)

let c_app_v v l = C_app_var (v,l)
let c_app_id id l = C_app_id (id,l)
let c_app_builtin b l = C_app_builtin (b,l)
let c_val v = C_val v

module Print : sig
  val print_expr : expr printer
  val print_val : value printer
  val print_computation : computation printer
end = struct
  let print_expr _ _ = assert false
  and print_val _ _ = assert false
  and print_computation _ _ = assert false
end

(** Environment for evaluation, with definitions of datatypes and
  functions, and other axioms *)
type env = (expr, value, [`Nested]) Env.t

(** {2 Conversion from {!NunTermPoly} *)

exception InvalidProblem of string
(** Raised when a problem cannot be converted into a narrowing problem *)

let () = Printexc.register_printer
  (function
    | InvalidProblem msg -> Some ("invalid problem for narrowing: " ^ msg)
    | _ -> None
  )

module OfPoly(T : NunTermInner.REPR) : sig
  module TPoly : module type of NunTermPoly.Make(T)

  val conv_pb: (TPoly.t, TPoly.t, [`Nested]) NunProblem.t -> env * expr
  (** [conv_pb pb] returns a pair [env, goal] where [goal] is the goal
    of [pb] after conversion into ANF, and [env] is an environment suitable
    for evaluation.
    @raise InvalidProblem if the translation fails. *)
end = struct
  module TPoly = NunTermPoly.Make(T)

  let conv_pb _ = assert false (* TODO: traverse + flatten defs *)
end


