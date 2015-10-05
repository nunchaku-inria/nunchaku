
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Conversion from {!NunTerm_typed} to {!NunTerm_ho}} *)

module Stmt = NunStatement
module TI1 = NunTerm_typed
module TI2 = NunTerm_ho
module Var = NunVar

module type S = sig
  module T1 : NunTerm_typed.S
  module T2 : NunTerm_ho.S

  val convert : T1.t -> T2.t

  val convert_ty : T1.Ty.t -> T2.Ty.t

  type statement1 = (T1.t, T1.Ty.t) NunStatement.t
  type statement2 = (T2.t, T2.Ty.t) NunStatement.t

  val convert_statement : statement1 -> statement2
  val convert_statement_list : statement1 list -> statement2 list

  val convert_problem : statement1 list -> (T2.t, T2.Ty.t) TI2.problem
end

module Make(T1 : NunTerm_typed.S)(T2 : NunTerm_ho.S)
: S with module T1 = T1 and module T2 = T2
= struct
  module T1 = T1
  module T2 = T2

  let rec convert t = match T1.view t with
    | TI1.Builtin b -> T2.builtin b
    | TI1.Const v -> T2.const v
    | TI1.Var v -> T2.var (convert_var v)
    | TI1.App (f,l) ->
        T2.app (convert f) (List.map convert l)
    | TI1.Fun (v,t) ->
        T2.fun_ (convert_var v) (convert t)
    | TI1.Forall (v,t) -> T2.forall (convert_var v) (convert t)
    | TI1.Exists (v,t) -> T2.forall (convert_var v) (convert t)
    | TI1.Let (v,t,u) -> T2.let_ (convert_var v) (convert t) (convert u)
    | TI1.TyKind -> failwith "TypedToHO: kind not supported"
    | TI1.TyType -> (T2.ty_type :> T2.t)
    | TI1.TyMeta _ -> failwith "TypedToHO: cannot convert meta-variables"
    | TI1.TyBuiltin b -> (T2.ty_builtin b : T2.ty :> T2.t)
    | TI1.TyArrow (a,b) -> (T2.ty_arrow (convert_ty a) (convert_ty b) : T2.ty :> T2.t)
    | TI1.TyForall (v,t) -> (T2.ty_forall (convert_var v) (convert_ty t) : T2.ty :> T2.t)

  and convert_ty t =
    T2.Ty.of_term_exn (convert (T1.Ty.to_term t))

  (* keep the same ID *)
  and convert_var v = Var.update_ty v ~f:convert_ty

  type statement1 = (T1.t, T1.Ty.t) NunStatement.t
  type statement2 = (T2.t, T2.Ty.t) NunStatement.t

  let convert_statement st = Stmt.map ~term:convert ~ty:convert_ty st

  let convert_statement_list = CCList.map convert_statement

  let convert_problem l =
    let module M = NunID.Map in
    let sigma, defs, l = List.fold_left
      (fun (sigma,defs,acc) st ->
        let st = convert_statement st in
        let sigma, defs = match Stmt.view st with
          | Stmt.Decl (id,ty) -> M.add id ty sigma, defs
          | Stmt.Def (id,ty,t) ->
              M.add id ty sigma, M.add id t defs
          | Stmt.Axiom _ -> sigma, defs
        in
        sigma, defs, st :: acc
      ) (M.empty, M.empty, []) l
    in
    { TI2.statements=List.rev l; signature=sigma; defs }
end
