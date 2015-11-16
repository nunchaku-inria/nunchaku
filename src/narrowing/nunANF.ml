
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Administrative Normal Form AST, for Narrowing} *)

module ID = NunID
module Var = NunVar
module Env = NunEnv
module Subst = Var.Subst
module Stmt = NunStatement

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
type expr =
  | Val of value
  | Let of t_var * computation * expr (** Shallow let *)
  | Match of t_var * expr cases (** Shallow match *)
  | Ite of t_var * expr * expr (** Shallow if/then/else *)
  | Forall of t_var * expr (** Introduce a new rigid variable *)
  | Exists of t_var * expr (** Introduce a new meta *)
  | And of expr list
  | Or of expr list

(** A value in WHNF, not evaluable further except by refining metas *)
and value =
  | True
  | False
  | App of id * value list (** Constructor *)
  | HOApp of t_var * value list (** higher-order application of opaque var *)
  | Var of t_var (** Typically, opaque constant, like an existential *)
  | Meta of expr var (** Existential variable *)
  | Fun of t_var * expr (** Function *)

(** Variable that has a type represented by [ty] *)
and t_var = ty var

(** A shallow computation *)
and computation =
  | C_app_var of t_var * value list (** [fun_var, args] *)
  | C_app_id of id * value list (** [fun_name, args] or constructor app *)
  | C_app_builtin of Builtin.t * value list
  | C_val of value (** Value, in which some variables might be substituted *)

(** A type *)
and ty =
  | TyApp of id * ty list
  | TyVar of ty var
  | TyForall of ty var * ty
  | TyArrow of ty * ty
  | TyType
  | TyKind
  | TyProp

type expr_top = {
  cell: expr;
  blocked: value var option;
    (* the variable to refine if we want to continue evaluating *)
}

(** {2 Utils} *)

let mk_top ~blck e = {cell=e; blocked=blck;}

let mk_val v = Val v
let mk_let v t u = Let (v,t,u)
let mk_match v l = Match (v,l)
let mk_ite a b c = Ite (a,b,c)

let v_true = True
let v_false = False
let v_app c l = App (c,l)
let v_const c = App (c, [])
let v_ho_app f l = HOApp (f,l)
let v_var v = Var v
let v_meta v = Meta v
let v_fun v t = Fun (v,t)

let c_app_v v l = C_app_var (v,l)
let c_app_id id l = C_app_id (id,l)
let c_app_builtin b l = C_app_builtin (b,l)
let c_val v = C_val v

let ty_app id l = TyApp (id,l)
let ty_const id = TyApp (id,[])
let ty_var v = TyVar v
let ty_forall v t = TyForall (v,t)
let ty_arrow a b = TyArrow (a,b)
let ty_type = TyType
let ty_kind = TyKind
let ty_prop = TyProp

module Print : sig
  val print_expr : expr printer
  val print_val : value printer
  val print_computation : computation printer
  val print_ty : ty printer
end = struct
  let print_expr _ _ = assert false
  and print_val _ _ = assert false
  and print_computation _ _ = assert false
  and print_ty _ _ = assert false
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
  module TI = NunTermPoly
  module TPoly = TI.Make(T)
  module P = NunTermInner.Print(T)

  let invalid_pb msg = raise (InvalidProblem msg)
  let invalid_pbf fmt = NunUtils.exn_ksprintf fmt ~f:invalid_pb

  let rec into_expr t : expr = match TPoly.repr t with
    | TI.Var v -> mk_val (v_var (trans_var v))
    | TI.Const id -> mk_val (v_const id)
    | TI.App (_,_)
    | TI.AppBuiltin (_,_)
    | TI.Bind (_,_,_)
    | TI.Let (_,_,_)
    | TI.Match (_,_)
    | TI.TyBuiltin _
    | TI.TyArrow (_,_) -> assert false

  (* convert type *)
  and into_ty t : ty = match TPoly.repr t with
    | TI.Var v -> ty_var (trans_var v)
    | TI.Const id -> ty_const id
    | TI.App (f, l) ->
        (* convert head *)
        begin match into_ty f with
        | TyApp (id, l1) -> ty_app id (l1 @ List.map into_ty l)
        | _ -> invalid_pbf "term `@[%a@]` is not a type" P.print t
        end
    | TI.TyArrow (a,b) ->  ty_arrow (into_ty a) (into_ty b)
    | TI.Bind (`TyForall, v, t) ->
        let v = trans_var v in
        ty_forall v (into_ty t)
    | TI.TyBuiltin `Type -> ty_type
    | TI.TyBuiltin `Kind -> ty_kind
    | TI.TyBuiltin `Prop -> ty_prop
    | TI.Let _
    | TI.AppBuiltin _
    | TI.Bind _
    | TI.Match _ -> invalid_pbf "term `@[%a@]` is not a type" P.print t

  and trans_var v = Var.update_ty v ~f:into_ty

  (* convert statement and add it to [env] if it makes sense *)
  let convert_statement (env,maybe_goal) st = match Stmt.view st with
    | Stmt.Goal g ->
        begin match maybe_goal with
        | Some _ -> invalid_pb "several goals in the input"
        | None ->
            let g' = into_expr g in
            env, Some g'
        end
    | _ -> assert false (* TODO *)

  let conv_pb pb =
    let env = Env.create() in
    let env, maybe_goal =
      NunProblem.statements pb
      |> CCVector.fold convert_statement (env, None)
    in
    match maybe_goal with
    | None -> invalid_pb "no goal in the input"
    | Some g -> env, g
end


