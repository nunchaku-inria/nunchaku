
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Terms for Narrowing} *)

module ID = NunID
module Var = NunVar
module Env = NunEnv
module Subst = Var.Subst
module DBEnv = NunDBEnv
module Const = NunEvalConst

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

(** A term, using De Bruijn indices *)
and term =
  | App of term * term list
  | DB of ty DB.t
  | Meta of t_meta
  | Const of term Const.t
  | Builtin of Builtin.t
  | Let of ty * term * term
  | Bind of Binder.t * ty * term
  | Match of term * term cases
  | Ite of term * term * term
  | TyArrow of term * term

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
let let_ ~ty t u = Let (ty, t,u)
let bind b ~ty t = Bind (b,ty,t)
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

(** {2 Evaluation and Substitution} *)

type def_or_decl =
  | Local_def of ty * term lazy_t (* x := t : ty, [t] not evaluated yet *)
  | Local_decl of ty (* x : ty *)

let push_def ~ty t db = DBEnv.cons (Local_def (ty,t)) db
let push_decl ty db = DBEnv.cons (Local_decl ty) db

(* is [t] closed (meaning it has no free DB index)? *)
let db_closed t =
  let rec aux n t = match t with
  | App (f, l) -> aux n f && List.for_all (aux n) l
  | DB m -> m.DB.index < n
  | Meta v -> aux n (Var.ty v)
  | Const c ->
      assert (aux 0 c.Const.ty); true (* constant should have closed types *)
  | Builtin _ -> true
  | Let (ty,t,u) ->
      aux n ty  && aux n t && aux (n+1) u
  | Bind (_,ty,t) -> aux n ty && aux (n+1) t
  | Match (t,l) ->
      aux n t &&
      ID.Map.for_all
        (fun _ (tys,rhs) ->
          DBEnv.for_all (aux n) tys && aux (n+DBEnv.length tys) rhs)
        l
  | Ite (a,b,c) ->
      aux n a && aux n b && aux n c
  | TyArrow (a,b) -> aux n a && aux n b
  in
  aux 0 t

(* TODO: cache some [info] in each term, containing:
    - the number of binders needed for the term to be closed
      (allows for constant-time checking of closedness -> db_lift is id if closed)
*)

(* lift free DB indices in [t] by [n] ranks. *)
let db_lift n t =
  (* k: current depth *)
  let rec aux k old = match old with
    | App (f,l) ->
        let f' = aux k f in
        let l' = aux_l k l in
        if f==f' && l==l'  then old else app f' l'
    | DB v ->
        if v.DB.index < k
        then
          let ty' = aux k v.DB.ty in
          if v.DB.ty==ty' then old else db {v with DB.ty=ty'}
        else
          (* shift [v.index] *)
          let ty' = aux k v.DB.ty in
          db {v with DB.ty=ty'; index=v.DB.index + n; }
    | Meta v ->
        let ty' = aux k (Var.ty v) in
        if Var.ty v==ty' then old
        else meta (Var.update_ty v ~f:(fun _ -> ty'))
    | Const c ->
        let ty' = aux k c.Const.ty in
        if c.Const.ty==ty' then old else const (Const.set_ty c ~ty:ty')
    | Builtin _ -> old
    | Let (ty,t,u) ->
        (* expand [let]! *)
        let ty' = aux k ty in
        let t' = aux k t in
        let u' = aux (k+1) u in
        if ty==ty' && t==ty' && u==u' then old else let_ ~ty:ty' t' u'
    | Bind (b,ty,t) ->
        let ty' = aux k ty in
        let t' = aux (k+1) t in
        if ty==ty' && t==t' then old else bind b ~ty:ty' t'
    | Match (t,l) as old ->
        let t' = aux k t in
        let same = ref (t==t') in
        let l' = ID.Map.map
          (fun (tys, rhs) ->
            let tys' = DBEnv.map (aux k) tys in
            let rhs' = aux (k+ DBEnv.length tys) rhs in
            same := !same && DBEnv.for_all2 (==) tys tys' && rhs==rhs';
            tys', rhs')
          l
        in
        if !same then old else match_ t' l'
    | Ite (a,b,c) as old ->
        let a' = aux k a in
        let b' = aux k b in
        let c' = aux k c in
        if a==a' && b==b' && c==c' then old else ite a' b' c'
    | TyArrow (a,b) ->
        let a' = aux k a in
        let b' = aux k b in
        if a==a' && b==b' then old else ty_arrow a' b'
  and aux_l k l = match l with
    | [] -> []
    | t :: ts ->
        let t' = aux k t in
        let ts' = aux_l k ts in
        if t==t' && ts==ts' then l else t'::ts'
  in
  if n=0 then t else aux 0 t

(** [db_eval ~env t] evaluates [t] in the De Bruijn environment [env],
    that is, it expands variables that are bound with [Local_def]. *)
let rec db_eval
: env:def_or_decl DBEnv.t -> term -> term
= fun ~env old -> match old with
  | App (f,l) ->
      let f' = db_eval ~env f in
      let l' = db_eval_l ~env l in
      if f==f' && l==l'  then old else app f' l'
  | DB v ->
      begin match DBEnv.nth env v.DB.index with
      | Local_decl _ -> old
      | Local_def (_,t') ->
          (* t' was defined in the environment where [v = 0]; here, [v.index]
              is the number of binders traversed since, so free variables
              of [t'] must be lifted by [v.index] too *)
          let t' = Lazy.force t' in
          db_lift v.DB.index t'
      end
  | Meta v ->
      let ty' = db_eval ~env (Var.ty v) in
      if Var.ty v==ty' then old
      else meta (Var.set_ty ~ty:ty' v)
  | Const c ->
      let ty' = db_eval ~env c.Const.ty in
      if c.Const.ty==ty' then old else const (Const.set_ty c ~ty:ty')
  | Builtin _ -> old
  | Let (ty,t,u) ->
      (* expand [let]! *)
      let ty' = db_eval ~env ty in
      let t' = db_eval ~env t in
      let env = push_decl ty' env in
      let u' = db_eval ~env u in
      if ty==ty' && t==ty' && u==u' then old else let_ ~ty:ty' t' u'
  | Bind (b,ty,t) ->
      let ty' = db_eval ~env ty in
      let env = DBEnv.cons (Local_decl ty) env in
      let t' = db_eval ~env t in
      if ty==ty' && t==t' then old else bind b ~ty:ty' t'
  | Match (t,l) as old ->
      let t' = db_eval ~env t in
      let same = ref (t==t') in
      let l' = ID.Map.map
        (fun (tys, rhs) ->
          let tys' = DBEnv.map (db_eval ~env) tys in
          let env = DBEnv.fold_right push_decl tys env in
          let rhs' = db_eval ~env rhs in
          same := !same && DBEnv.for_all2 (==) tys tys' && rhs==rhs';
          tys', rhs')
        l
      in
      if !same then old else match_ t' l'
  | Ite (a,b,c) as old ->
      let a' = db_eval ~env a in
      let b' = db_eval ~env b in
      let c' = db_eval ~env c in
      if a==a' && b==b' && c==c' then old else ite a' b' c'
  | TyArrow (a,b) ->
      let a' = db_eval ~env a in
      let b' = db_eval ~env b in
      if a==a' && b==b' then old else ty_arrow a' b'

and db_eval_l ~env l = match l with
  | [] -> []
  | t :: ts ->
      let t' = db_eval ~env t in
      let ts' = db_eval_l ~env ts in
      if t==t' && ts==ts' then l else t'::ts'

(** [subst_eval ~subst t] replaces meta-variables bound in [subst].
    It also lifts [t] if [(v -> t) in subst] *)
let subst_eval
: subst:subst -> term -> term
= fun ~subst:_ _ -> assert false (* TODO if needed *)

(** {2 Comparison} *)

let equal
: ?subst:subst -> env:def_or_decl DBEnv.t -> term -> term -> bool
= fun ?(subst=Subst.empty) ~env t1 t2 ->
  (* recursive comparison *)
  let rec eq env t1 t2 =
    t1 == t2 || match t1, t2 with
    | Meta v, _ when Subst.mem ~subst v -> eq env (Subst.find_exn ~subst v) t2
    | _, Meta v when Subst.mem ~subst v -> eq env t1 (Subst.find_exn ~subst v)
    | Meta v1, Meta v2 -> Var.equal v1 v2
    | App (f1,l1), App(f2,l2) ->
        List.length l1 = List.length l2 &&
        eq env f1 f2 &&
        List.for_all2 (eq env) l1 l2
    | _, _ -> assert false (* TODO *)
    | _ -> false
  in
  eq env t1 t2

(** {2 Toplevel Term}

  Term designed for WHNF evaluation. It focuses on the head because that
  is where evaluation takes place. The head is actually a subterm
  found under a number of "ifthenelse" and "match". *)

(* TODO: add a subst for meta-variables in the term *)

module TermTop : sig
  type t = private {
    cont: continuation;
    head: term;
    args: t list;
    env: def_or_decl DBEnv.t; (* variables declared or defined *)
  }
  and continuation =
    | K_apply
    | K_ite of term * term * continuation
    | K_match of term cases * continuation
  val of_term: env:def_or_decl DBEnv.t -> term -> t
  val of_term0 : term -> t (** empty env *)
  val make: ?cont:continuation -> env:def_or_decl DBEnv.t -> term -> t list -> t
  val set_head : ?cont:continuation -> t -> hd:term -> t
  val to_term: t -> term
  val env: t -> def_or_decl DBEnv.t
  val blocked: t -> t_meta option
    (** If the reduction is blocked by a meta [v], this returns [Some v] *)
end = struct
  type t = {
    cont: continuation;
    head: term;
    args: t list;
    env: def_or_decl DBEnv.t; (* variables declared or defined *)
  }
  (* encoding:
    - [K_ite (a,b,cont) head args] is [(cont (if head then a else b)) args]
    - [K_match (l,cont) head args] is [(cont (match head with ...l...)) args]
    - [K_apply head args] is [head args]
  *)

  and continuation =
    | K_apply
    | K_ite of term * term * continuation
    | K_match of term cases * continuation

  (* build recursively.
      @param the continuation *)
  let rec mk_ ~cont ~env ~args t = match t with
    | Ite (a,b,c) ->
        mk_ a ~cont:(K_ite (b,c,cont)) ~env ~args
    | Match (t,l) ->
        mk_ t ~cont:(K_match (l,cont)) ~env ~args
    | App (f, l) ->
        let args' = List.map (of_term ~env) l in
        let args = if args=[] then args' else args' @ args in
        mk_ f ~cont ~env ~args
    | _ ->
        {head=t; args; cont; env; }

  and of_term ~env t = mk_ t ~cont:K_apply ~env ~args:[]

  let of_term0 t = mk_ t ~cont:K_apply ~env:DBEnv.nil ~args:[]

  let make ?(cont=K_apply) ~env t args = mk_ ~cont ~env ~args t

  let env t = t.env

  let blocked t = match t.head with
    | Meta v -> Some v
    | _ -> None

  let set_head ?cont t ~hd =
    let cont = match cont with None -> t.cont | Some x -> x in
    mk_ hd ~env:t.env ~args:t.args ~cont

  (* convert back to a regular term *)
  let rec to_term t = app_rec_ t.cont t.head t.args
  and app_rec_ cont head args = match cont with
    | K_apply -> app head (List.map to_term args)
    | K_ite (a,b,cont') ->
        let head' = ite head a b in
        app_rec_ cont' head' args
    | K_match (l,cont') ->
        let head' = match_ head l in
        app_rec_ cont' head' args
end

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
