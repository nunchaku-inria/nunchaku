
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Skolemization} *)

module ID = NunID
module TI = NunTerm_intf
module Var = NunVar
module T = NunTerm_ho

type id = NunID.t

let section = NunUtils.Section.make "skolem"

module type S = sig
  module T1 : NunTerm_ho.REPR
  module T2 : NunTerm_ho.S

  type 'i state

  val create : ?prefix:string -> unit -> 'i state
  (** @param prefix the prefix used to generate Skolem symbols *)

  val nnf : 'inv T1.t -> 'inv T2.t
  (** Put term in negation normal form *)

  val skolemize : state:'i state -> 'i T2.t -> 'i T2.t * (id * 'i T2.t) list
  (** [skolemize ~state t] returns [t', new_syms] where [t'] is
      the skolemization of [t], and [new_syms] is a set of new symbols
      with their type *)

  val print_state : Format.formatter -> _ state -> unit

  val convert_problem :
    state:'i state ->
    ('i T1.t, 'i T1.t, 'inv) NunProblem.t ->
    ('i T2.t, 'i T2.t, 'inv) NunProblem.t

  val find_id_def : state:'i state -> id -> 'i T2.t option
  (** Find definition of this Skolemized ID *)

  val decode_model :
    state:'i state -> 'i T2.t NunModel.t -> 'i T2.t NunModel.t

  val pipe :
    print:bool ->
    (('inv T1.t,'inv T1.t,'inv_p) NunProblem.t,
      ('inv T2.t,'inv T2.t,'inv_p) NunProblem.t,
      'inv T2.t NunModel.t, 'inv T2.t NunModel.t
    ) NunTransform.t

  (** Similar to {!pipe} but with a generic decode function.
      @param decode is given [find_id_def], which maps Skolemized
        constants to the formula they define *)
  val pipe_with :
    decode:(find_id_def:(id -> 'inv T2.t option) -> 'c -> 'd) ->
    print:bool ->
    (('inv T1.t,'inv T1.t,'inv_p) NunProblem.t,
      ('inv T2.t,'inv T2.t,'inv_p) NunProblem.t, 'c, 'd
    ) NunTransform.t
end

module Make(T1 : NunTerm_ho.REPR)(T2 : NunTerm_ho.S)
: S with module T1 = T1 and module T2 = T2
= struct
  module T1 = T1
  module T2 = T2
  module U = NunTerm_ho.Util(T2)

  module Subst = NunVar.Subst
  module Stmt = NunStatement

  type 'i new_sym = {
    sym_defines : 'i T2.t; (* what is the formula represented by the symbol *)
    sym_ty : 'i T2.t; (* type of the symbol *)
  }

  type 'i state = {
    tbl: 'i new_sym ID.Tbl.t; (* skolem -> quantified form *)
    prefix:string; (* prefix for Skolem symbols *)
    mutable name : int;
    mutable new_sym: (id * 'i new_sym) list; (* list of newly defined symbols *)
  }

  let create ?(prefix="nun_sk_") () = {
    tbl=ID.Tbl.create 32;
    prefix;
    name=0;
    new_sym=[];
  }

  type 'i env = {
    vars: 'i T2.t Var.t list;  (* variables on the path *)
    subst: ('i T2.t, 'i T2.t) Subst.t; (* substitution for existential variables *)
  }

  let env_bind ~env v t =
    { env with subst=Subst.add ~subst:env.subst v t }

  let env_add_var ~env v =
    { env with vars=v :: env.vars }

  let new_sym ~state =
    let n = state.name in
    state.name <- n+1;
    ID.make ~name:(state.prefix ^ string_of_int n)

  module B = NunBuiltin.T
  let mk_not a = U.app_builtin B.Not [a]
  let mk_and a b = U.app_builtin B.And [a;b]
  let mk_or a b = U.app_builtin B.Or [a;b]
  let mk_ite a b c = U.app_builtin B.Ite [a;b;c]

  (* first, negation normal form *)
  let rec nnf
  : type inv. inv T1.t -> inv T2.t
  = fun t -> match T1.repr t with
    | TI.Const id -> U.const id
    | TI.Var v -> U.var (nnf_var_ v)
    | TI.TyVar v -> U.ty_var (nnf_var_ v)
    | TI.App (f,l) -> U.app (nnf f) (List.map nnf l)
    | TI.AppBuiltin (b,l) ->
        begin match b, l with
        | B.True, _ -> U.builtin B.True
        | B.False, _ -> U.builtin B.False
        | B.Or, _
        | B.And, _
        | B.Ite, _
        | B.Eq, _ -> U.app_builtin b (List.map nnf l)
        | B.Imply, [a;b] -> mk_or (nnf_neg a) (nnf b)
        | B.Equiv, [a;b] -> (* a => b & b => a *)
            mk_and (mk_or (nnf_neg a) (nnf b)) (mk_or (nnf_neg b) (nnf a))
        | B.Not, [f] -> nnf_neg f
        | _ -> assert false
        end
    | TI.Bind (k,v,t) -> U.mk_bind k (nnf_var_ v) (nnf t)
    | TI.Let (v,t,u) ->
        U.let_ (nnf_var_ v) (nnf t) (nnf u)
    | TI.Match (t,l) ->
        U.match_with (nnf t)
          (ID.Map.map (fun (vars,rhs) -> List.map nnf_var_ vars,nnf rhs) l)
    | TI.TyBuiltin b -> U.ty_builtin b
    | TI.TyArrow (a,b) -> U.ty_arrow (nnf a) (nnf b)
    | TI.TyMeta _ -> assert false

  (* negation + negation normal form *)
  and nnf_neg
  : type inv. inv T1.t -> inv T2.t
  = fun t -> match T1.repr t with
    | TI.Const id -> mk_not (U.const id)
    | TI.Var v -> mk_not (U.var (nnf_var_ v))
    | TI.TyVar v -> mk_not (U.ty_var (nnf_var_ v))
    | TI.App (f,l) -> mk_not (U.app (nnf f) (List.map nnf l))
    | TI.AppBuiltin (b,l) ->
        begin match b, l with
        | B.True, _ -> U.builtin B.False
        | B.False, _ -> U.builtin B.True
        | B.Or, l -> U.app_builtin B.And (List.map nnf_neg l)
        | B.And, l -> U.app_builtin B.Or (List.map nnf_neg l)
        | B.Ite, [a;b;c] ->
            mk_ite (nnf a) (nnf_neg b) (nnf_neg c)
        | B.Eq, _ -> mk_not (U.app_builtin b (List.map nnf l))
        | B.Imply, [a;b] ->
            mk_and (nnf a) (nnf_neg b)  (* a & not b *)
        | B.Equiv, [a;b] -> (* not a & b | not b & a *)
            mk_or (mk_and (nnf_neg a) (nnf b)) (mk_and (nnf_neg b) (nnf a))
        | B.Not, [f] -> nnf f (* not not f -> f *)
        | _ -> assert false
        end
    | TI.Bind (TI.Forall, v,t) -> U.exists (nnf_var_ v) (nnf_neg t)
    | TI.Bind (TI.Exists, v,t) -> U.forall (nnf_var_ v) (nnf_neg t)
    | TI.Bind (TI.Fun,_,_) -> failwith "cannot skolemize function"
    | TI.Bind (TI.TyForall,_,_) -> failwith "cannot skolemize `ty_forall`"
    | TI.Let (v,t,u) ->
        U.let_ (nnf_var_ v) (nnf t) (nnf u)
    | TI.Match _ ->
        mk_not (nnf t)
    | TI.TyBuiltin b -> U.ty_builtin b
    | TI.TyArrow (a,b) -> U.ty_arrow (nnf a) (nnf b)
    | TI.TyMeta _ -> assert false

  and nnf_var_
  : type inv. inv T1.t Var.t -> inv T2.t Var.t
  = fun v -> Var.update_ty v ~f:nnf

  let skolemize_
  : type inv. state:inv state -> inv T2.t -> inv T2.t
  = fun ~state t ->
    (* recursive traversal *)
    let rec aux
    : env:inv env -> inv T2.t -> inv T2.t
    = fun ~env t -> match T2.repr t with
      | TI.Const id -> U.const id
      | TI.Var v ->
          begin match Subst.find ~subst:env.subst v with
            | None -> U.var (aux_var ~env v)
            | Some t -> t
          end
      | TI.TyVar v ->
          begin match Subst.find ~subst:env.subst v with
            | None -> U.ty_var (aux_var ~env v)
            | Some t -> t
          end
      | TI.AppBuiltin (b,l) ->
          begin match b, l with
          | B.True, _
          | B.False, _ -> t
          | B.Not, [f] -> mk_not (aux ~env f)
          | B.Or, _
          | B.And, _
          | B.Ite, _
          | B.Eq, _ ->
              U.app_builtin b (List.map (aux ~env) l)
          | B.Imply, _
          | B.Equiv, _ -> assert false
          | _ -> assert false
          end
      | TI.App (f,l) ->
          U.app (aux ~env f) (List.map (aux ~env) l)
      | TI.Bind (TI.TyForall, v, t) ->
          (* FIXME: here we know U.invariant_poly = T1.invariant_poly = polymorph
             but the typechecker isn't aware. *)
          enter_var_ ~env v
            (fun env v -> U.mk_bind TI.TyForall v (aux ~env t))
      | TI.Bind ((TI.Fun | TI.Forall) as b, v, t) ->
          enter_var_ ~env v
            (fun env v -> U.mk_bind b v (aux ~env t))
      | TI.Bind (TI.Exists, v, t') ->
          (* type of Skolem function *)
          let ty_ret = aux ~env (Var.ty v) in
          let ty_args = List.map Var.ty env.vars in
          let ty = List.fold_right U.ty_arrow ty_args ty_ret in
          (* create new skolem function *)
          let skolem_id = new_sym ~state in
          let skolem = U.app (U.const skolem_id) (List.map U.var env.vars) in
          let new_sym = { sym_defines=t; sym_ty=ty } in
          ID.Tbl.add state.tbl skolem_id new_sym;
          state.new_sym <- (skolem_id, new_sym):: state.new_sym;
          NunUtils.debugf ~section 2
            "@[<2>new Skolem symbol `%a :@ @[%a@]` standing for@ @[`%a`@]@]"
            (fun k-> k ID.print_no_id skolem_id
                (T.print_ty ~repr:T2.repr) ty (T.print ~repr:T2.repr) t);
          (* convert [t] and replace [v] with [skolem] in it *)
          let env = env_bind ~env v skolem in
          aux ~env t'
      | TI.Let (v,t,u) ->
          let t = aux ~env t in
          enter_var_ ~env v (fun env v -> U.let_ v t (aux ~env u))
      | TI.Match (t, l) ->
          let t = aux ~env t in
          let l = ID.Map.map
            (fun (vars,rhs) ->
              let env, vars' = NunUtils.fold_map
                (fun env v ->
                  let v' = aux_var ~env v in
                  let env = env_add_var ~env v' in
                  env, v'
                ) env vars
              in
              vars', aux ~env rhs
            ) l
          in
          U.match_with t l
      | TI.TyBuiltin b -> U.ty_builtin b
      | TI.TyArrow (a,b) -> U.ty_arrow (aux ~env a) (aux ~env b)
      | TI.TyMeta _ -> assert false

    and aux_var
    : env:inv env -> inv T2.t Var.t -> inv T2.t Var.t
    = fun ~env v -> Var.update_ty ~f:(aux ~env) v

    and enter_var_
    : type a.
        env:inv env -> inv T2.t Var.t -> (inv env -> inv T2.t Var.t -> a) -> a
    = fun ~env v f ->
      let v' = aux_var ~env v in
      let env = env_add_var ~env v' in
      f env v'
    in
    let env = {
      vars=[];
      subst=Subst.empty;
    } in
    aux ~env t

  let skolemize ~state t =
    let t' = skolemize_ ~state t in
    (* clear list of new symbols *)
    let l = state.new_sym in
    state.new_sym <- [];
    t', List.map (fun (id,s) -> id,s.sym_ty) l

  let convert_problem ~state pb =
    NunProblem.map_with
      ~before:(fun () ->
        let l = state.new_sym in
        state.new_sym <- [];
        List.map
          (fun (id,s) -> Stmt.decl ~info:Stmt.info_default id s.sym_ty)
          l
      )
      ~term:(fun t -> skolemize_ ~state (nnf t))
      ~ty:(fun t -> skolemize_ ~state (nnf t))
      pb

  let fpf = Format.fprintf

  let print_state out st =
    let pp_sym out (id,s) =
      fpf out "@[<2>%a: %a@ standing for `@[%a@]`@]"
        ID.print_no_id id
          (T.print_ty ~repr:T2.repr) s.sym_ty
          (T.print ~repr:T2.repr) s.sym_defines
    in
    fpf out "@[<2>skolem table {@,%a@]@,}"
      (CCFormat.seq pp_sym) (ID.Tbl.to_seq st.tbl)

  let epsilon = ID.make ~name:"_witness_of"

  let find_id_def ~state id =
    (* if [id] is a Skolem symbol, use an epsilon to display the
      existential formula it is the witness of *)
    try
      let sym = ID.Tbl.find state.tbl id in
      let f = sym.sym_defines in
      Some (U.app (U.const epsilon) [f])
    with Not_found -> None

  let decode_model ~state m =
    m |> List.map
        (fun (t,u) -> match T2.repr t with
          | TI.Const id ->
              begin match find_id_def ~state id with
                | None -> t, u
                | Some t' -> t', u
              end
          | _ -> t, u
        )

  let pipe_with ~decode ~print =
    let on_encoded = if print
      then
        [Format.printf "@[<v2>after Skolemization: %a@]@."
          (NunProblem.print
            ~pt_in_app:(T.print_in_app ~repr:T2.repr)
            ~pty_in_app:(T.print_in_app ~repr:T2.repr)
            (T.print ~repr:T2.repr) (T.print_ty ~repr:T2.repr))]
      else []
    in
    NunTransform.make1
      ~name:"skolem"
      ~on_encoded
      ~print:print_state
      ~encode:(fun pb ->
        let state = create() in
        let pb = convert_problem ~state pb in
        pb, state
      )
      ~decode:(fun state x ->
        decode ~find_id_def:(find_id_def ~state) x
      )
      ()

  let pipe ~print =
    let decode ~find_id_def m =
      m |> List.map
          (fun (t,u) -> match T2.repr t with
            | TI.Const id ->
                begin match find_id_def id with
                  | None -> t, u
                  | Some t' -> t', u
                end
            | _ -> t, u
          )
    in
    pipe_with ~decode ~print
end
