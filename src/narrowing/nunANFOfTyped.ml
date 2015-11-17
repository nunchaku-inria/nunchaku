
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Conversion from {!NunTermTyped} to {!NunANF}
  
  Types are useful for introducing intermediate variables
  that will stand for sub-expressions. *)

module ID = NunID
module Var = NunVar
module Env = NunEnv
module Stmt = NunStatement
module ANF = NunANF
module Meta = ANF.Meta

(** Environment for evaluation, with definitions of datatypes and
  functions, and other axioms *)
type env = (ANF.expr, ANF.value, [`Nested]) Env.t

exception InvalidProblem of string
(** Raised when a problem cannot be converted into a narrowing problem *)

let () = Printexc.register_printer
  (function
    | InvalidProblem msg -> Some ("invalid problem for narrowing: " ^ msg)
    | _ -> None
  )

module Convert(T : NunTermTyped.REPR) : sig
  val conv_pb: (T.t, T.t, [`Nested]) NunProblem.t -> env * ANF.expr
  (** [conv_pb pb] returns a pair [env, goal] where [goal] is the goal
    of [pb] after conversion into ANF, and [env] is an environment suitable
    for evaluation.
    @raise InvalidProblem if the translation fails. *)
end = struct
  module TI = NunTermInner
  module P = NunTermInner.Print(T)
  module U = NunTermTyped.Util

  let invalid_pb msg = raise (InvalidProblem msg)
  let invalid_pbf fmt = NunUtils.exn_ksprintf fmt ~f:invalid_pb

  module VVarSet = ANF.VVarSet

  type ctx = {
    env: env; (* context for identifiers *)
  }

  (* convert type *)
  let rec into_ty t : ANF.ty = match T.repr t with
    | TI.Var v -> ANF.ty_var (trans_var v)
    | TI.Const id -> ANF.ty_const id
    | TI.App (f, l) ->
        (* convert head *)
        begin match into_ty f with
        | ANF.TyApp (id, l1) -> ANF.ty_app id (l1 @ List.map into_ty l)
        | _ -> invalid_pbf "term `@[%a@]` is not a type" P.print t
        end
    | TI.TyArrow (a,b) ->  ANF.ty_arrow (into_ty a) (into_ty b)
    | TI.Bind (`TyForall, v, t) ->
        let v = trans_var v in
        ANF.ty_forall v (into_ty t)
    | TI.TyBuiltin `Type -> ANF.ty_type
    | TI.TyBuiltin `Kind -> ANF.ty_kind
    | TI.TyBuiltin `Prop -> ANF.ty_prop
    | TI.TyMeta _ -> assert false (* should have been inferred *)
    | TI.Let _
    | TI.AppBuiltin _
    | TI.Bind _
    | TI.Match _ -> invalid_pbf "term `@[%a@]` is not a type" P.print t

  and trans_var v = Var.update_ty v ~f:into_ty

  (* type of a term *)
  let ty_ t = match T.ty t with
    | None -> assert false
    | Some ty -> into_ty ty

  (* is the [id] a constructor? *)
  let is_cstor_ ~ctx id = match Env.find ~env:ctx.env id with
    | None -> invalid_pbf "identifier %a not declared" ID.print_name id
    | Some {Env.def=Env.Cstor _;_} -> true
    | Some _ -> false

  (* convert [t] into an expression
      @param k a continuation that is given the value of this expression
        to continue the computation *)
  let rec into_expr ~ctx t k : ANF.expr = match T.repr t with
    | TI.Var v -> k (ANF.v_var (trans_var v))
    | TI.Const id -> k (ANF.v_const id)
    | TI.App (f, []) -> into_expr ~ctx f k
    | TI.App (f, l) ->
        into_expr ~ctx f
          (fun f' ->
            into_expr_l ~ctx l (fun l' ->
              assert (l' <> []);
              ANF.apply_v_v f' l'
            )
          )
    | TI.AppBuiltin (_,_)
    | TI.Bind (_,_,_)
    | TI.Let (_,_,_)
    | TI.Match (_,_)
    | TI.TyBuiltin _
    | TI.TyArrow (_,_) -> assert false

  and into_expr_l ~ctx l k = match l with
    | [] -> assert false
    | [t] -> into_expr ~ctx t (fun t' -> k [t'])
    | t :: l' ->
        into_expr ~ctx t
          (fun t' ->
            into_expr_l ~ctx l' (fun l'' -> k (t' :: l'')))
  (* convert statement and add it to [env] if it makes sense *)
  let convert_statement (env,maybe_goal) st =
    let ctx = {env} in
    match Stmt.view st with
    | Stmt.Goal g ->
        begin match maybe_goal with
        | Some _ -> invalid_pb "several goals in the input"
        | None ->
            let g' = into_expr ~ctx g ANF.mk_val in
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
