
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

(** {2 Meta-Variables} *)
module Meta : sig
  type 'a t = private 'a var
  val make : ty:'a -> name:string -> 'a t
  val fresh_copy : 'a t -> 'a t
end = struct
  type 'a t = 'a var
  let make = Var.make
  let fresh_copy = Var.fresh_copy
end

type 'a case = 'a var list * 'a
type 'a cases = 'a case ID.Map.t

(** ['a] paired with a type *)
type 'a typed = {
  mutable cell: 'a;
  mutable ty: ty option;
  closure: subst; (* closure: propagated to sub-terms *)
}

(** A type *)
and ty = ty_cell typed
and ty_cell =
  | TyApp of id * ty list
  | TyVar of ty var
  | TyForall of ty var * ty
  | TyArrow of ty * ty
  | TyType
  | TyKind
  | TyProp

(** Variable that has a type represented by [ty] *)
and t_var = ty var
and t_meta = ty Meta.t

(** A nested program, chaining computations. *)
and expr = expr_cell typed
and expr_cell =
  | Val of value
  | Let of t_var * computation * expr (** Shallow let *)
  | Match of t_var * expr cases (** Shallow match *)
  | Ite of t_var * expr * expr (** Shallow if/then/else *)
  | Forall of t_var * expr (** Introduce a new rigid variable *)
  | Exists of t_var * expr (** Introduce a new meta *)
  | And of expr list
  | Or of expr list
  | Imply of expr * expr

(** A value in WHNF, not evaluable further except by refining metas *)
and value = value_cell typed
and value_cell =
  | True
  | False
  | App of id * value list
      (** Application of constructor or opaque (uninterpreted) constant *)
  | Var of t_var
      (** Variable to be substituted, of a non-functional type *)
  | Fun of fun_
      (** Function. Never applied, otherwise it would β reduce *)

(** A shallow computation *)
and computation =
  | C_val of value (** Value, in which some variables might be substituted *)
  | C_app_meta of t_meta * value list (** [fun_var, args] *)
  | C_app_var of t_var * value list (** [fun_var, args] *)
  | C_app_id of id * value list (** [fun_name, args]. [id] is {b NOT} a constructor  *)
  | C_app_fun of fun_ * value (** apply the function *)
  | C_eq of t_var * t_var (** Unify *)

(** A function is an expression parametrized over a variable *)
and fun_ = {
  fun_arg: t_var;
  fun_body: expr;
}

(** Substitution *)
and subst = (ty, value) Subst.t

type expr_top = {
  cell: expr;
  blocked: value var option;
    (* the variable to refine if we want to continue evaluating *)
}

(** {2 Utils} *)

let mk_top ~blck e = {cell=e; blocked=blck;}

(* TODO: hashcons types? *)

let ty_app id l = TyApp (id,l)
let ty_const id = TyApp (id,[])
let ty_var v = TyVar v
let ty_forall v t = TyForall (v,t)
let ty_arrow a b = TyArrow (a,b)
let ty_type = TyType
let ty_kind = TyKind
let ty_prop = TyProp

let e_val v = Val v
let e_let v t u = Let (v,t,u)
let e_match v l = Match (v,l)
let e_ite a b c = Ite (a,b,c)
let e_and l = And l
let e_or l = Or l
let e_imply a b = Imply (a,b)

let v_true = True
let v_false = False
let v_var v = Var v
let v_app c l = App (c,l)
let v_const c = App (c, [])
let v_fun f = Fun f

let c_val v = C_val v
let c_app_var v l = C_app_var (v,l)
let c_app_meta v l = C_app_meta (v,l)
let c_app_id id l = C_app_id (id,l)
let c_app_fun f x = C_app_fun (f, x)
let c_eq a b = C_eq (a,b)

let fun_ v body = {fun_arg=v; fun_body=body;}

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

module VVarSet = Var.Set(struct type t = ty end)

let ty_apply

let rec apply_v_v
: value -> value list -> (value -> expr) -> expr
= fun f l k ->
  match f with
  | ANF.App (id, l1) ->
      (* non-reducing application *)
      k (ANF.v_app id (l1 @ l))
  | ANF.Var v ->
      (* variable of functional type:
         transform  [k (v l)] into
        [let v' = c_app_var v l in k v' *)
      let v' = Var.make ~name:"v" ~ty:(ty_ t) in
      ANF.e_let v' (ANF.c_app_var v l) (k (ANF.v_var v'))
  | ANF.Fun f ->
      (* actual function:
        transform  [k (f (a :: l'))] into
        [let v' = c_app_fun f a in k (v' l') *)
      let a, l' = match l with [] -> assert false | x::y->x,y in
      let v1 = Var.make ~name:"v1" ~ty:(ty_ t) in
      ANF.e_let v' (ANF.c_app_fun f a)
        (
        (k (ANF.v_var v'))
  | ANF.True
  | ANF.False -> assert false (* type error *)

