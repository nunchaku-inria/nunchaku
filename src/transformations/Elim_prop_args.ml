
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Eliminate function arguments of type "prop"} *)

open Nunchaku_core

module TI = TermInner
module T = Term
module TyI = TypeMono
module Ty = TypeMono.Make(T)
module Stmt = Statement
module PStmt = Stmt.Print(T)(T)

type term = T.t
type ty = T.t
type problem = (term, ty) Problem.t
type model = (term,ty) Model.t
type res = (term,ty) Problem.Res.t

let name = "elim_prop_args"
let section = Utils.Section.make name

(* names of the pseudo-boolean identifiers *)
type state = {
  true_ : ID.t;
  false_ : ID.t;
  pseudo_prop: ID.t;
  env: (term,ty) Env.t;
  new_sig : ty ID.Tbl.t; (* types after translation *)
}

let create_state ~env () =
  let st = {
    true_ = ID.make "true_";
    false_ = ID.make "false_";
    pseudo_prop = ID.make "prop_";
    env;
    new_sig=ID.Tbl.create 25;
  } in
  ID.Tbl.add st.new_sig st.pseudo_prop T.ty_type;
  let ty_pprop = T.ty_const st.pseudo_prop in
  ID.Tbl.add st.new_sig st.true_ ty_pprop;
  ID.Tbl.add st.new_sig st.false_ ty_pprop;
  st

(** {2 Encoding} *)

(* statements that declare the pseudo-prop type *)
let declare_ state : (_,_) Stmt.t list =
  let ty_pprop = T.ty_const state.pseudo_prop in
  let ptrue = T.const state.true_ in
  let pfalse = T.const state.false_ in
  let mk_decl ?(attrs=[]) id ty =
    Stmt.decl ~info:Stmt.info_default ~attrs id ty
  in
  let decl_ty =
    mk_decl
      ~attrs:[Stmt.Attr_pseudo_prop;
              Stmt.Attr_card_min_hint 2;
              Stmt.Attr_card_max_hint 2]
      state.pseudo_prop (T.ty_builtin `Type)
  and decl_true =
    mk_decl state.true_ ty_pprop
      ~attrs:[Stmt.Attr_pseudo_true]
  and decl_false = mk_decl state.false_ ty_pprop
  and distinct_ax =
    Stmt.axiom1 ~info:Stmt.info_default
      (T.neq ptrue pfalse)
  and exhaustive_ax =
    let x = Var.make ~name:"x" ~ty:ty_pprop in
    Stmt.axiom1 ~info:Stmt.info_default
      (T.forall x
         (T.or_ [T.eq (T.var x) ptrue; T.eq (T.var x) pfalse]))
  in
  [ decl_ty; decl_true; decl_false; distinct_ax; exhaustive_ax ]

let find_ty state (t:term) : ty = T.ty_exn ~env:state.env t

(* translate a type
   @param top true if toplevel; only toplevel props are
     preserved *)
let transform_ty state ~top ty =
  let rec aux top ty = match Ty.repr ty with
    | TyI.Builtin `Prop ->
      if top then ty
      else T.const state.pseudo_prop
    | TyI.Builtin _
    | TyI.Const _ -> ty
    | TyI.Arrow (a,b) ->
      (* [b] might still be toplevel *)
      T.ty_arrow (aux false a) (aux top b)
    | TyI.App (f,l) ->
      T.ty_app (aux false f) (List.map (aux false) l)
  in
  aux top ty

(* find the new type of an ID *)
let find_new_ty state (t:term) : ty =
  T.ty_of_signature_exn t
    ~sigma:(fun id -> ID.Tbl.get state.new_sig id)

(* rename [v], and maybe update its type from [prop] to [pseudo_prop], since
   we cannot quantify on propositions *)
and transform_var state v =
  let v' = Var.fresh_copy v in
  Var.update_ty v'
    ~f:(transform_ty state ~top:false)

let rename_var state subst v =
  let v' = transform_var state v in
  Var.Subst.add ~subst v v', v'

(* does [t : prop]? *)
let has_ty_prop_ state t : bool =
  let ty = find_ty state t in
  T.ty_is_Prop ty

let get_true_ state : T.t = T.const state.true_
let get_false_ state : T.t = T.const state.false_

(* TODO: rewrite this as a type-driven pass:
   - carry around old_env, new_env
   - recurse in subterms, translate them, infer their new type
   - if new type is prop and we expect prop_, use `ite`
     if new type is prop_ and we expect prop, use `= true_`
     (careful with builtins, in particular boolean ones)
*)

let ty_is_pseudo_prop state ty = T.equal ty (T.const state.pseudo_prop)

(* traverse a term, replacing any argument [a : prop]
   with [if a then pseudo_true else pseudo_false];
   also, change variables' types: no boolean variable should remain *)
let transform_term state subst t =
  let wrap_prop t : T.t =
    T.ite t (get_true_ state) (get_false_ state)
  in
  (* translate [t], keeping its toplevel type unless it is
     a boolean variable *)
  let rec aux_top subst t = match T.repr t with
    | TI.Const _ -> t
    | TI.Var v ->
      (* no toplevel propositional variable *)
      if T.ty_is_Prop (Var.ty v)
      then T.eq (aux_expect_prop' subst t) (get_true_ state)
      else (
        let v' = Var.Subst.find_exn ~subst v in
        T.var v'
      )
    | TI.App (f, l) ->
      (* translate head and arguments *)
      let _, ty_args, _ = find_ty state f |> T.ty_unfold in
      let f' = aux_top subst f in
      assert (List.length l = List.length ty_args);
      let l' =
        List.map2
          (fun arg ty ->
             if T.ty_is_Prop ty
             then aux_expect_prop' subst arg (* argument position *)
             else aux_top subst arg)
          l
          ty_args
      in
      T.app f' l'
    | TI.Builtin (`Eq (a,b)) when has_ty_prop_ state a ->
      (* transform [a <=> b] into [a = b] where [a:prop_] *)
      T.eq (aux_expect_prop' subst a) (aux_expect_prop' subst b)
    | TI.Let (v, t, u) ->
      begin match T.repr u with
        | TI.Var v' when Var.equal v v' -> aux_top subst t (* subst on the fly *)
        | _ ->
          (* might have to change [v]'s type *)
          let new_v =
            Var.fresh_copy v
            |> Var.update_ty ~f:(transform_ty state ~top:false)
          in
          (* if [v] was a boolean, it now has to be a pseudo prop,
             which means [t] might have to be wrapped *)
          let new_t =
            if ty_is_pseudo_prop state (Var.ty new_v)
            then aux_expect_prop' subst t
            else aux_top subst t
          in
          let subst = Var.Subst.add ~subst v new_v in
          let new_u = aux_top subst u in
          T.let_ new_v new_t new_u
      end
    | TI.Builtin `True -> T.true_
    | TI.Builtin `False -> T.false_
    | TI.Builtin ((`Not _ | `And _ | `Or _ | `Imply _ | `Eq _) as b) ->
      (* boolean formulas are ok *)
      let b = Builtin.map b ~f:(aux_top subst) in
      T.builtin b
    | TI.Builtin (`Undefined_self t) -> T.undefined_self (aux_top subst t)
    | TI.Builtin (`Guard (t,g)) ->
      let t' = aux_top subst t in
      let g' = Builtin.map_guard (aux_top subst) g in
      T.guard t' g'
    | TI.Bind ((Binder.Forall | Binder.Exists) as b, v, body) ->
      let subst, v = rename_var state subst v in
      T.mk_bind b v (aux_top subst body)
    | TI.Builtin (`Undefined_atom _|`Ite _|`DataTest _
                 |`DataSelect _|`Unparsable _|`Card_at_least _)
    | TI.Bind ((Binder.Fun|Binder.TyForall|Binder.Mu), _, _)
    | TI.Match (_, _, _) | TI.TyBuiltin _ | TI.TyArrow (_, _)
      ->
      (* cannot have boolean args, translation can proceed *)
      T.map subst t
        ~bind:(rename_var state) ~f:aux_top
    | TI.TyMeta _ -> assert false

  (* we expect a term of type [prop'] after translation *)
  and aux_expect_prop' subst t = match T.repr t with
    | TI.Var v ->
      let v' = Var.Subst.find_exn ~subst v in
      assert (ty_is_pseudo_prop state (Var.ty v'));
      T.var v' (* no casting needed *)
    | TI.Builtin `True -> get_true_ state
    | TI.Builtin `False -> get_false_ state
    | TI.Builtin (`Not _ | `And _ | `Or _ | `Imply _ | `Eq _) ->
      (* prop: wrap in if/then/else *)
      let t' = aux_top subst t in
      wrap_prop t'
    | TI.Builtin (`Guard (t,g)) ->
      let new_t = aux_expect_prop' subst t in
      let new_g = Builtin.map_guard (aux_top subst) g in
      T.guard new_t new_g
    | _ ->
      (* we expect [prop'], see what we get by translating [t] *)
      let new_t = aux_top subst t in
      let new_ty = find_new_ty state new_t in
      if ty_is_pseudo_prop state new_ty
      then new_t
      else (
        assert (T.ty_is_Prop new_ty);
        wrap_prop new_t
      )
  in
  aux_top subst t

let transform_statement state stmt : (_,_) Stmt.t =
  Utils.debugf ~section 3 "@[<2>transform @{<cyan>statement@}@ `@[%a@]`@]"
    (fun k->k PStmt.pp stmt);
  (* how to translate a "defined" *)
  let tr_defined d =
    Stmt.map_defined d ~f:(transform_ty state ~top:true)
  in
  (* declare new symbols {b before} processing [stmt]: it makes it
     easier to deal with recursive definitions *)
  begin
    Stmt.defined_seq stmt
    |> Iter.map tr_defined
    |> Iter.iter
      (fun d -> ID.Tbl.add state.new_sig d.Stmt.defined_head d.Stmt.defined_ty);
  end;
  (* new statement, + [true] if the statement was already declared *)
  let stmt' = match Stmt.view stmt with
    | Stmt.Copy _ -> assert false (* precond *)
    | Stmt.Decl _
    | Stmt.TyDef (_,_)
    | Stmt.Axiom _
    | Stmt.Goal _
    | Stmt.Pred (_,_,_) ->
      Stmt.map_bind Var.Subst.empty stmt
        ~bind:(rename_var state)
        ~term:(fun subst _pol -> transform_term state subst)
        ~ty:(fun _ -> transform_ty state ~top:true)
  in
  stmt'

let transform_problem pb =
  let env = Problem.env pb in
  let state = create_state ~env () in
  (* insert additional declarations before the first statement *)
  let prelude = declare_ state in
  let pb' =
    Problem.map_statements pb
      ~prelude ~f:(transform_statement state)
  in
  pb', state

(** {2 Decoding} *)

module M = Model
module DT = M.DT

type rewrite = {
  rw_true: ID.t;
  rw_false: ID.t;
}

let find_rewrite state m : rewrite option =
  let id_true, id_false =
    Model.fold (None,None) m
      ~values:(fun (id_true,id_false) (t,dt,_) -> match dt with
        | DT.Yield u ->
          begin match T.repr t, T.repr u with
            | TI.Const id, TI.Const id' when ID.equal id state.true_ ->
              assert (id_true = None);
              Some id', id_false
            | TI.Const id, TI.Const id' when ID.equal id state.false_ ->
              assert (id_false = None);
              id_true, Some id'
            | _ -> id_true, id_false
          end
        | _ -> id_true, id_false
      )
  in
  match id_true, id_false with
    | None, None -> None
    | Some id1, Some id2 -> Some { rw_true=id1; rw_false=id2; }
    | Some _, None
    | None, Some _ ->
      failwith
        "elim_prop_args: model contains one of true_,false_ but not both"

(* decoding terms:
   - find constants corresponding to pseudo-prop true and false
   - collapse pseudo-prop into prop *)
let decode_term state rw t =
  let rec aux t = match T.repr t, rw with
    | TI.Const id, _ when ID.equal id state.true_ -> T.true_
    | TI.Const id, _ when ID.equal id state.false_ -> T.false_
    | TI.Const id, _ when ID.equal id state.pseudo_prop -> T.ty_prop
    | TI.Const id, Some rw when ID.equal id rw.rw_true -> T.true_
    | TI.Const id, Some rw when ID.equal id rw.rw_false -> T.false_
    | TI.Var v, _ -> T.var (aux_var v)
    | _ ->
      T.map () t
        ~bind:(fun () v -> (), aux_var v)
        ~f:(fun () -> aux)
  and aux_var v =
    Var.update_ty ~f:aux v
  in
  aux t

let decode_model state m =
  let rw = find_rewrite state m in
  let tr_term = decode_term state rw in
  Model.filter_map m
    ~finite_types:(fun (ty,dom) -> match T.repr ty with
      | TI.Const id when ID.equal id state.pseudo_prop -> None
      | _ -> Some (tr_term ty, dom))
    ~values:(fun (t,dt,k) -> match T.repr t with
      | TI.Const id when (ID.equal id state.true_ || ID.equal id state.false_) ->
        None (* drop pseudo-booleans from model *)
      | _ ->
        let t = tr_term t in
        let dt = DT.map dt ~ty:tr_term ~term:tr_term in
        Some (t, dt, k)
    )

(** {2 Pipes} *)

let pipe_with ?on_decoded ~decode ~print ~check () =
  let on_encoded =
    Utils.singleton_if print () ~f:(fun () ->
      let module PPb = Problem.P in
      Format.printf "@[<v2>@{<Yellow>after %s@}: %a@]@." name PPb.pp)
    @
      Utils.singleton_if check ()
        ~f:(fun () ->
          let module C = TypeCheck.Make(T) in
          C.empty () |> C.check_problem)
  in
  Transform.make
    ~name
    ~input_spec:Transform.Features.(of_list
          [Ind_preds, Absent; Ty, Mono; Eqn, Absent;
           Copy, Absent; Pseudo_prop, Absent;
           If_then_else, Present; HOF, Absent])
    ~map_spec:Transform.Features.(update_l [Prop_args, Absent; Pseudo_prop, Present])
    ~on_encoded
    ?on_decoded
    ~encode:transform_problem
    ~decode
    ()

let pipe ~print ~check =
  let on_decoded = if print
    then
      [Format.printf "@[<2>@{<Yellow>res after %s@}:@ %a@]@."
         name (Problem.Res.pp T.pp' T.pp)]
    else []
  in
  let decode state = Problem.Res.map_m ~f:(decode_model state) in
  pipe_with ~on_decoded ~decode ~print ~check ()
