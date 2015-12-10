
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Skolemization} *)

module ID = ID
module TI = TermInner
module Var = Var

type id = ID.t

let section = Utils.Section.make "skolem"

module type S = sig
  module T1 : TI.REPR
  module T2 : TI.S

  type state

  val create : ?prefix:string -> unit -> state
  (** @param prefix the prefix used to generate Skolem symbols *)

  val nnf : T1.t -> T2.t
  (** Put term in negation normal form *)

  val skolemize : state:state -> T2.t -> T2.t * (id * T2.t) list
  (** [skolemize ~state t] returns [t', new_syms] where [t'] is
      the skolemization of [t], and [new_syms] is a set of new symbols
      with their type *)

  val print_state : Format.formatter -> state -> unit

  val convert_problem :
    state:state ->
    (T1.t, T1.t, <eqn:_;ind_preds:_;..> as 'inv) Problem.t ->
    (T2.t, T2.t, 'inv) Problem.t

  val find_id_def : state:state -> id -> T2.t option
  (** Find definition of this Skolemized ID *)

  val decode_model :
    state:state -> T2.t Model.t -> T2.t Model.t

  val pipe :
    print:bool ->
    ((T1.t,T1.t,<eqn:_;ind_preds:_;..> as 'inv) Problem.t,
      (T2.t,T2.t,'inv) Problem.t,
      T2.t Model.t, T2.t Model.t
    ) Transform.t

  (** Similar to {!pipe} but with a generic decode function.
      @param decode is given [find_id_def], which maps Skolemized
        constants to the formula they define *)
  val pipe_with :
    decode:(state -> 'c -> 'd) ->
    print:bool ->
    ((T1.t,T1.t, <eqn:_;ind_preds:_;..> as 'inv) Problem.t,
      (T2.t,T2.t,'inv) Problem.t, 'c, 'd
    ) Transform.t
end

module Make(T1 : TI.REPR)(T2 : TI.S)
: S with module T1 = T1 and module T2 = T2
= struct
  module T1 = T1
  module T2 = T2
  module U = TI.Util(T2)
  module P2 = TI.Print(T2)

  module Subst = Var.Subst
  module Stmt = Statement

  type new_sym = {
    sym_defines : T2.t; (* what is the formula represented by the symbol *)
    sym_ty : T2.t; (* type of the symbol *)
  }

  type state = {
    tbl: new_sym ID.Tbl.t; (* skolem -> quantified form *)
    prefix:string; (* prefix for Skolem symbols *)
    mutable name : int;
    mutable new_sym: (id * new_sym) list; (* list of newly defined symbols *)
  }

  let create ?(prefix="nun_sk_") () = {
    tbl=ID.Tbl.create 32;
    prefix;
    name=0;
    new_sym=[];
  }

  type env = {
    vars: T2.t Var.t list;  (* variables on the path *)
    subst: (T2.t, T2.t) Subst.t; (* substitution for existential variables *)
  }

  let env_bind ~env v t =
    { env with subst=Subst.add ~subst:env.subst v t }

  let env_add_var ~env v =
    { env with vars=v :: env.vars }

  let new_sym ~state =
    let n = state.name in
    state.name <- n+1;
    ID.make (state.prefix ^ string_of_int n)

  let mk_and a b = U.and_ [a;b]
  let mk_or a b = U.or_ [a;b]

  (* first, negation normal form *)
  let rec nnf t = match T1.repr t with
    | TI.Const id -> U.const id
    | TI.Var v -> U.var (nnf_var_ v)
    | TI.App (f,l) ->
        begin match T1.repr f, l with
        | TI.Builtin (
          (`True | `False | `Or | `And | `Ite _ | `Eq _ | `Equiv _) as b), _ ->
            U.app_builtin (TI.Builtin.map ~f:nnf b) (List.map nnf l)
        | TI.Builtin `Imply, [a;b] -> mk_or (nnf_neg a) (nnf b)
        | TI.Builtin `Not, [f] -> nnf_neg f
        | _ -> U.app (nnf f) (List.map nnf l)
        end
    | TI.Builtin (`Equiv (a,b)) -> (* a => b & b => a *)
        mk_and (mk_or (nnf_neg a) (nnf b)) (mk_or (nnf_neg b) (nnf a))
    | TI.Builtin b -> U.builtin (TI.Builtin.map b ~f:nnf)
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
  and nnf_neg t = match T1.repr t with
    | TI.Const id -> U.not_ (U.const id)
    | TI.Var v -> U.not_ (U.var (nnf_var_ v))
    | TI.App (f,l) ->
        begin match T1.repr f, l with
        | TI.Builtin `Or, l -> U.app_builtin `And (List.map nnf_neg l)
        | TI.Builtin `And, l -> U.app_builtin `Or (List.map nnf_neg l)
        | TI.Builtin `Imply, [a;b] ->
            mk_and (nnf a) (nnf_neg b)  (* a & not b *)
        | TI.Builtin `Not, [f] -> nnf f (* not not f -> f *)
        | _ -> U.not_ (U.app (nnf f) (List.map nnf l))
        end
    | TI.Builtin `True -> U.builtin `False
    | TI.Builtin `False -> U.builtin `True
    | TI.Builtin (`Ite (a,b,c)) ->
        U.ite (nnf a) (nnf_neg b) (nnf_neg c)
    | TI.Builtin (`Equiv (a,b)) -> (* not a & b | not b & a *)
        mk_or (mk_and (nnf_neg a) (nnf b)) (mk_and (nnf_neg b) (nnf a))
    | TI.Builtin b -> U.not_ (U.builtin (TI.Builtin.map ~f:nnf b))
    | TI.Bind (`Forall, v,t) -> U.exists (nnf_var_ v) (nnf_neg t)
    | TI.Bind (`Exists, v,t) -> U.forall (nnf_var_ v) (nnf_neg t)
    | TI.Bind (`Fun,_,_) -> failwith "cannot skolemize function"
    | TI.Bind (`TyForall,_,_) -> failwith "cannot skolemize `ty_forall`"
    | TI.Let (v,t,u) ->
        U.let_ (nnf_var_ v) (nnf t) (nnf u)
    | TI.Match _ ->
        U.not_ (nnf t)
    | TI.TyBuiltin b -> U.ty_builtin b
    | TI.TyArrow (a,b) -> U.ty_arrow (nnf a) (nnf b)
    | TI.TyMeta _ -> assert false

  and nnf_var_ v = Var.update_ty v ~f:nnf

  let skolemize_ ~state t =
    (* recursive traversal *)
    let rec aux ~env t = match T2.repr t with
      | TI.Const id -> U.const id
      | TI.Var v ->
          begin match Subst.find ~subst:env.subst v with
            | None -> U.var (aux_var ~env v)
            | Some t -> t
          end
      | TI.Builtin (`True | `False) -> t
      | TI.Builtin (`Equiv _) -> assert false
      | TI.Builtin
        ((`Eq _ | `Ite _ | `Imply | `DataSelect _
           | `DataTest _ | `Undefined _ | `Polarized _ | `And | `Or | `Not) as b) ->
          U.builtin (TI.Builtin.map b ~f:(aux ~env))
      | TI.App (f,l) ->
          begin match T2.repr f, l with
          | TI.Builtin `Not, [f] -> U.not_ (aux ~env f)
          | TI.Builtin ((`Or | `And | `Imply) as b), _ ->
              U.app_builtin b (List.map (aux ~env) l)
          | _ -> U.app (aux ~env f) (List.map (aux ~env) l)
          end
      | TI.Bind (`TyForall, v, t) ->
          (* FIXME: here we know U.invariant_poly = T1.invariant_poly = polymorph
             but the typechecker isn't aware. *)
          enter_var_ ~env v
            (fun env v -> U.mk_bind `TyForall v (aux ~env t))
      | TI.Bind ((`Fun | `Forall) as b, v, t) ->
          enter_var_ ~env v
            (fun env v -> U.mk_bind b v (aux ~env t))
      | TI.Bind (`Exists, v, t') ->
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
          Utils.debugf ~section 2
            "@[<2>new Skolem symbol `%a :@ @[%a@]` standing for@ @[`%a`@]@]"
            (fun k-> k ID.print skolem_id P2.print ty P2.print t);
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
              let env, vars' = Utils.fold_map
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

    and aux_var ~env v = Var.update_ty ~f:(aux ~env) v

    and enter_var_ ~env v f =
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
    Problem.map_with
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
        ID.print id P2.print s.sym_ty P2.print s.sym_defines
    in
    fpf out "@[<2>skolem table {@,%a@]@,}"
      (CCFormat.seq pp_sym) (ID.Tbl.to_seq st.tbl)

  let epsilon = ID.make "_witness_of"

  let find_id_def ~state id =
    (* if [id] is a Skolem symbol, use an epsilon to display the
      existential formula it is the witness of *)
    try
      let sym = ID.Tbl.find state.tbl id in
      let f = sym.sym_defines in
      Some (U.app (U.const epsilon) [f])
    with Not_found -> None

  let decode_model ~state m =
    Model.filter_map m
      ~finite_types:(fun (ty,dom) -> Some (ty,dom))
      ~terms:(fun (t,u) ->
          match T2.repr t with
          | TI.Const id ->
              begin match find_id_def ~state id with
                | None -> Some (t, u)
                | Some t' -> Some (t', u)
              end
          | _ -> Some (t, u)
        )

  let pipe_with ~decode ~print =
    let on_encoded = if print
      then
        let module P = Problem.Print(P2)(P2) in
        [Format.printf "@[<v2>after Skolemization: %a@]@." P.print]
      else []
    in
    Transform.make1
      ~name:"skolem"
      ~on_encoded
      ~print:print_state
      ~encode:(fun pb ->
        let state = create() in
        let pb = convert_problem ~state pb in
        pb, state
      )
      ~decode
      ()

  let pipe ~print =
    pipe_with ~decode:(fun state m -> decode_model ~state m) ~print
end
