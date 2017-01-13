
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Skolemization} *)

open Nunchaku_core

module TI = TermInner
module Pol = Polarity
module Subst = Var.Subst
module Stmt = Statement
module T = TI.Default
module U = T.U
module P = T.P

type term = TermInner.Default.t

let name = "skolem"
let section = Utils.Section.make name

(* for direct translation *)
module Conv = TI.Convert(T)(T)

type new_sym = {
  sym_defines : T.t; (* what is the formula represented by the symbol *)
  sym_decode: bool; (* record for the model? *)
  sym_ty : T.t; (* type of the symbol *)
}

type mode =
  [ `Sk_types (** Skolemize type variables only *)
  | `Sk_ho (** Skolemize type variables and term variables of fun type *)
  | `Sk_all (** All variables are susceptible of being skolemized *)
  ]

type state = {
  mutable env: (T.t,T.t) Env.t;
  tbl: new_sym ID.Tbl.t; (* skolem -> quantified form *)
  prefix:string; (* prefix for Skolem symbols *)
  mode: mode;
  mutable name : int;
  mutable new_sym: (ID.t * new_sym) list; (* list of newly defined symbols *)
}

let create ?(prefix="nun_sk_") ~mode () = {
  env=Env.create ();
  tbl=ID.Tbl.create 32;
  prefix;
  mode;
  name=0;
  new_sym=[];
}

type env = {
  vars: T.t Var.t list;  (* variables on the path *)
  subst: (T.t, T.t) Subst.t; (* substitution for existential variables *)
}

let env_bind ~env v t =
  { env with subst=Subst.add ~subst:env.subst v t }

let env_add_var ~env v =
  { env with vars=v :: env.vars }

let new_sym ~state =
  let n = state.name in
  state.name <- n+1;
  ID.make (state.prefix ^ string_of_int n)

(* TODO: maybe transform nested `C[if exists x.p[x] then a else b]` where `a`
   is not of type prop, into `exists x.p[x] => C[a] & ¬ exists x.p[x] => C[b]` *)

(* shall we skolemize the existential variable [v]? *)
let should_skolemize_ ~state v =
  let ty = Var.ty v in
  match state.mode, T.repr ty with
  | `Sk_all, _ -> true
  | (`Sk_types | `Sk_ho), TI.TyBuiltin `Type -> true
  | `Sk_types, _ -> false
  | `Sk_ho, TI.TyArrow _ -> true
  | `Sk_ho, _ -> false

let skolemize_ ~state ?(in_goal=false) pol t =
  (* recursive traversal *)
  let rec aux env pol t = match T.repr t with
    | TI.Const id -> U.const id
    | TI.Var v ->
        begin match Subst.find ~subst:env.subst v with
          | None -> U.var (aux_var env v)
          | Some t -> t
        end
    | TI.Bind ((`Exists | `Forall) as b, v, t') ->
        begin match b, pol with
        | `Exists, Pol.Pos
        | `Forall, Pol.Neg when should_skolemize_ ~state v ->
            (* type of Skolem function *)
            let ty_ret = aux env Pol.NoPol (Var.ty v) in
            let ty_args = List.map Var.ty env.vars in
            let ty = List.fold_right U.ty_arrow ty_args ty_ret in
            (* create new skolem function *)
            let skolem_id = new_sym ~state in
            let skolem = U.app (U.const skolem_id) (List.map U.var env.vars) in
            let new_sym = { sym_defines=t; sym_decode=in_goal; sym_ty=ty } in
            ID.Tbl.add state.tbl skolem_id new_sym;
            state.new_sym <- (skolem_id, new_sym):: state.new_sym;
            Utils.debugf ~section 2
              "@[<2>new Skolem symbol `%a :@ @[%a@]` standing for@ @[`%a`@]@]"
              (fun k-> k ID.print skolem_id P.print ty P.print t);
            (* convert [t] and replace [v] with [skolem] in it *)
            let env = env_bind ~env v skolem in
            aux env pol t'
        | _ ->
            let env = env_add_var ~env v in
            U.mk_bind b v (aux env pol t')
        end
    | TI.Let (v, t, u) ->
      (* rename [v], but do not parametrize skolems with it *)
      let t' = aux env pol t in
      let v' = aux_var env v in
      let env' = env_bind ~env v (U.var v') in
      let u' = aux env' pol u in
      U.let_ v' t' u'
    | TI.App _
    | TI.Builtin _
    | TI.Bind _
    | TI.Match _
    | TI.TyArrow _ ->
        aux' env pol t
    | TI.TyBuiltin b -> U.ty_builtin b
    | TI.TyMeta _ -> assert false

  and aux' env pol t =
    U.map_pol env pol t
      ~f:aux
      ~bind:(fun env v ->
        let v' = aux_var env v in
        let env = env_add_var ~env v' in
        env, v')

  and aux_var env v = Var.update_ty ~f:(aux env Pol.NoPol) v in

  let env = {
    vars=[];
    subst=Subst.empty;
  } in
  aux env pol t

let skolemize ~state ?in_goal pol t =
  let t' = skolemize_ ~state ?in_goal pol t in
  (* clear list of new symbols *)
  let l = state.new_sym in
  state.new_sym <- [];
  t', List.map (fun (id,s) -> id,s.sym_ty) l

let skolemize_stmt ~state st =
  let info = Stmt.info st in
  let sk_term ?in_goal () pol t = skolemize_ ~state ?in_goal pol t in
  match Stmt.view st with
  | Stmt.Axiom (Stmt.Axiom_std l) ->
      Stmt.axiom ~info (List.map (sk_term () Pol.Pos) l)
  | Stmt.Axiom (Stmt.Axiom_spec l) ->
      let l = Stmt.map_spec_defs ~term:(sk_term () Pol.Pos) ~ty:CCFun.id l in
      Stmt.axiom_spec ~info l
  | Stmt.Axiom (Stmt.Axiom_rec l) ->
      let l = Stmt.map_rec_defs_bind () l
          ~bind:(fun () v->(),v) ~ty:(fun () ty->ty)
          ~term:(sk_term ~in_goal:false)
      in
      Stmt.axiom_rec ~info l
  | Stmt.Pred (wf, kind, l) ->
      let l = Stmt.map_preds_bind () l 
          ~bind:(fun () v->(),v) ~ty:(fun () ty ->ty)
          ~term:(sk_term ~in_goal:false)
      in
      Stmt.mk_pred ~info ~wf kind l
  | Stmt.Goal g ->
      Stmt.goal ~info (sk_term ~in_goal:true () Pol.Pos g)
  | Stmt.Copy _
  | Stmt.TyDef _
  | Stmt.Decl _ -> st

let skolemize_pb ~state pb =
  Problem.flat_map_statements
    ~f:(fun stmt ->
      let stmt' = skolemize_stmt ~state stmt in
      state.env <- Env.add_statement ~env:state.env stmt';
      let l = state.new_sym in
      state.new_sym <- [];
      let prelude =
        List.map
          (fun (id,s) -> Stmt.decl ~info:Stmt.info_default ~attrs:[] id s.sym_ty)
          l
      in
      List.rev_append prelude [stmt'])
    pb

let fpf = Format.fprintf

let print_state out st =
  let pp_sym out (id,s) =
    fpf out "@[<2>%a: %a@ standing for `@[%a@]`@]"
      ID.print id P.print s.sym_ty P.print s.sym_defines
  in
  fpf out "@[<2>skolem table {@,%a@]@,}"
    (CCFormat.seq pp_sym) (ID.Tbl.to_seq st.tbl)

let epsilon = ID.make "_witness_of"

let find_id_def ~state id =
  (* if [id] is a Skolem symbol, use an epsilon to display the
    existential formula it is the witness of *)
  try
    let sym = ID.Tbl.find state.tbl id in
    Some sym
  with Not_found -> None

let decode_model ~skolems_in_model ~state m =
  Model.filter_map m
    ~finite_types:(fun (ty,dom) -> Some (ty,dom))
    ~values:(fun ((t,dt,k) as tup) ->
      match T.repr t with
        | TI.Const id ->
            begin match find_id_def ~state id with
              | None -> Some tup
              | Some sym ->
                if sym.sym_decode && skolems_in_model
                then
                  let t' = U.app_const epsilon [sym.sym_defines] in
                  Some (t',dt,k)
                else None (* ignore  this symbol *)
            end
        | _ -> Some tup)

let pipe_with ~mode ~decode ~print ~check =
  let on_encoded =
    Utils.singleton_if print ()
      ~f:(fun () ->
        let module Ppb = Problem.Print(P)(P) in
        Format.printf "@[<v2>@{<Yellow>after Skolemization@}: %a@]@." Ppb.print)
    @
    Utils.singleton_if check ()
      ~f:(fun () ->
         let module C = TypeCheck.Make(T) in
         C.empty () |> C.check_problem)
  in
  Transform.make
    ~name
    ~on_encoded
    ~print:print_state
    ~encode:(fun pb ->
      let state = create ~mode () in
      let pb = skolemize_pb ~state pb in
      pb, state
    )
    ~decode
    ()

let pipe ~skolems_in_model ~mode ~print ~check =
  pipe_with ~check ~mode ~print
    ~decode:(fun state ->
      Problem.Res.map_m
        ~f:(decode_model ~skolems_in_model ~state))
