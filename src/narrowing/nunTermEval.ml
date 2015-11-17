
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Terms for Narrowing} *)

module ID = NunID
module Var = NunVar
module Env = NunEnv
module Subst = Var.Subst
module DBEnv = NunDBEnv

type id = ID.t
type 'a var = 'a Var.t
type 'a printer = Format.formatter -> 'a -> unit

let fpf = Format.fprintf

(** {2 De Bruijn indices} *)
module DB = struct
  type 'ty t = {
    name: string;
    index: int;
    ty: 'ty;
  }

  let make ~name ~ty n = {name; ty; index=n; }
end

(** {2 Terms} *)

module Builtin = struct
  type t =
    [ `Eq
    | `Imply
    | `Equiv
    | `And
    | `Or
    | `Not
    | `True
    | `False
    | `Type
    | `Kind
    | `Prop
    ]
end

module Binder = struct
  type t =
    [ `Forall
    | `Exists
    | `Fun
    | `TyForall
    ]
end

(** List of types for each bound De Bruijn *)
type 'a case = 'a DBEnv.t * 'a

type 'a cases = 'a case ID.Map.t

type const = {
  const_id: id; (* symbol *)
  const_ty: ty; (* type of symbol *)
  const_def: def; (* definition/declaration for the symbol *)
}
and def =
  | Cstor of ty * const list (* datatype it belongs to + list of all constructors *)
  | Def of term (* id == this term *)
  | Datatype of const list (* list of constructors *)
  | Opaque
  (* TODO: DefNode of term * node, for memoization *)

(** A term, using De Bruijn indices *)
and term =
  | App of term * term list
  | DB of ty DB.t
  | Meta of t_meta
  | Const of const
  | Builtin of Builtin.t
  | Let of term * term
  | Bind of Binder.t * term
  | Match of term * term cases
  | Ite of term * term * term
  | TyArrow of term * term
  | TyBuiltin of [`Prop | `Kind | `Type]

and ty = term

(** Variable that has a type represented by [ty] *)
and t_meta = ty var

(** Substitution *)
and subst = (term, term) Subst.t

module VarSet = Var.Set(struct type t = ty end)

let app f l = match f, l with
  | _, [] -> f
  | App (f1,l1), _ -> App (f1, l1 @ l)
  | _ -> App (f,l)
let db v = DB v
let meta v = Meta v
let const c = Const c
let builtin b = Builtin b
let app_builtin b l = app (builtin b) l
let let_ t u = Let (t,u)
let bind b t = Bind (b,t)
let match_ t l = Match (t,l)
let ite a b c = Ite(a,b,c)

let forall t = bind `Forall t
let exists t = bind `Exists t
let fun_ t = bind `Fun t
let ty_forall t = bind `TyForall t

let ty_arrow a b = TyArrow (a,b)
let type_ = builtin `Type
let kind = builtin `Kind
let prop = builtin `Prop

let not_ t = app_builtin `Not [t]
let imply a b = app_builtin `Imply [a;b]
let eq a b = app_builtin `Eq [a;b]
let and_ l = app_builtin `And l
let or_ l = app_builtin `Or l
let true_ = builtin `True
let false_ = builtin `False

type term_top = {
  cell: term;
  env: ty DBEnv.t; (* variables that are bound but not defined *)
  subst: term DBEnv.t; (* terms introduced by "let" *)
  blocked: VarSet.t;
    (* the meta-variable to refine if we want to continue evaluating *)
}

(** {2 Utils} *)

module Print : sig
  val print : term printer
  val print_ty : ty printer
end = struct
  let print _ _ = assert false
  and print_ty _ _ = assert false
end

(*
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

  *)
