
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Eliminate function arguments of type "prop"} *)

open Nunchaku_core

module TI = TermInner
module T = TI.Default
module U = T.U
module P = T.P
module TyI = TypeMono
module Ty = TypeMono.Make(T)
module Stmt = Statement
module PStmt = Stmt.Print(P)(P)

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
  sigma: ty Signature.t;
  mutable declared: bool; (* did we declare prop_? *)
  mutable needed: bool; (* do we need prop_? *)
}

let create_state ~sigma () =
  { true_ = ID.make "true_";
    false_ = ID.make "false_";
    pseudo_prop = ID.make "prop_";
    declared = false;
    needed = false;
    sigma;
  }

(** {2 Encoding} *)

(* statements that declare the pseudo-prop type *)
let declare_ state : (_,_) Stmt.t list =
  assert (not state.declared);
  state.declared <- true;
  let mk_decl ?(attrs=[]) id ty =
    Stmt.decl ~info:Stmt.info_default ~attrs id ty
  in
  let decl_ty =
    mk_decl
      ~attrs:[Stmt.Attr_pseudo_prop;
              Stmt.Attr_card_hint (Cardinality.of_int 2)]
      state.pseudo_prop (U.ty_builtin `Type)
  and decl_true =
    mk_decl state.true_ (U.ty_const state.pseudo_prop)
      ~attrs:[Stmt.Attr_pseudo_true]
  and decl_false = mk_decl state.false_ (U.ty_const state.pseudo_prop)
  and distinct_ax =
    Stmt.axiom1 ~info:Stmt.info_default
      (U.not_
         (U.eq (U.const state.true_) (U.const state.false_)))
  in
  [ decl_ty; decl_true; decl_false; distinct_ax ]

let find_ty state (t:term) : ty =
  U.ty_exn ~sigma:(Signature.find ~sigma:state.sigma) t

(* translate a type
   @param top true if toplevel; only toplevel props are
     preserved *)
let rec transform_ty state ~top ty =
  let rec aux top ty = match Ty.repr ty with
    | TyI.Builtin `Prop ->
      if top then ty
      else (
        state.needed <- true;
        U.const state.pseudo_prop
      )
    | TyI.Builtin _
    | TyI.Const _ -> ty
    | TyI.Arrow (a,b) ->
      (* [b] might still be toplevel *)
      U.ty_arrow (aux false a) (aux top b)
    | TyI.App (f,l) ->
      U.ty_app (aux false f) (List.map (aux false) l)
  in
  aux top ty

(* rename [v], and maybe update its type from [prop] to [pseudo_prop], since
   we cannot quantify on propositions *)
and transform_var state v =
  let v' = Var.fresh_copy v in
  Var.update_ty v'
    ~f:(transform_ty state ~top:false)

let rename_var state subst v =
  let v' = transform_var state v in
  Var.Subst.add ~subst v v', v'

(* TODO: rewrite this as a type-driven pass:
   - carry around old_sigma, new_sigma
   - recurse in subterms, translate them, infer their new type
   - if new type is prop and we expect prop_, use `ite`
     if new type is prop_ and we expect prop, use `= true_`
     (careful with builtins, in particular boolean ones)
  *)

(* does [t : prop]? *)
let has_ty_prop_ state t : bool =
  let ty = find_ty state t in
  U.ty_is_Prop ty

let get_true_ state : T.t = state.needed <- true; U.const state.true_
let get_false_ state : T.t = state.needed <- true; U.const state.false_

(* traverse a term, replacing any argument [a : prop]
   with [if a then pseudo_true else pseudo_false];
   also, change variables' types *)
let transform_term state subst t =
  (* translate [t], keeping its toplevel type  *)
  let rec aux subst t = match T.repr t with
    | TI.Var v ->
      (* no toplevel propositional variable *)
      if U.ty_is_Prop (Var.ty v)
      then U.eq (aux_expect_prop' subst t) (get_true_ state)
      else (
        let v' = Var.Subst.find_exn ~subst v in
        U.var v'
      )
    | TI.App (f, l) ->
      let ty_f = find_ty state f in
      let _, ty_args, _ = U.ty_unfold ty_f in
      (* translate head and arguments *)
      let f' = aux subst f in
      assert (List.length l = List.length ty_args);
      let l' =
        List.map2
          (fun arg ty ->
             if U.ty_is_Prop ty
             then aux_expect_prop' subst arg
             else aux subst arg)
          l
          ty_args
      in
      U.app f' l'
    | TI.Builtin (`Eq (a,b)) when has_ty_prop_ state a ->
      (* transform [a <=> b] into [a = b] where [a:prop_] *)
      U.eq (aux_expect_prop' subst a) (aux_expect_prop' subst b)
    | _ ->
      U.map subst t
        ~bind:(rename_var state) ~f:aux
(* we expect [t] to have type [prop_] after translation *)
  and aux_expect_prop' subst t = match T.repr t with
    | TI.Var v ->
      assert state.needed;
      let v' = Var.Subst.find_exn ~subst v in
      assert (U.equal (Var.ty v') (U.const state.pseudo_prop));
      U.var v' (* no casting needed *)
    | TI.Builtin `True -> get_true_ state
    | TI.Builtin `False -> get_false_ state
    | TI.Builtin (`Not _ | `And _ | `Or _ | `Imply _ | `Eq _) ->
      (* prop: wrap in if/then/else *)
      let t' = aux subst t in
      wrap_prop t'
    | TI.Builtin (`Guard (t,g)) ->
      let t' = aux_expect_prop' subst t in
      let g' = TI.Builtin.map_guard (aux subst) g in
      U.guard t' g'
    | TI.Builtin (`Ite _ | `DataTest _ | `DataSelect _
                 | `Undefined_atom _ | `Undefined_self _ | `Unparsable _) ->
      wrap_prop (aux subst t)
    | _ ->
      wrap_prop (aux subst t)
  and wrap_prop t : T.t =
    U.ite t (get_true_ state) (get_false_ state)
  in
  aux subst t

let transform_statement state st : (_,_) Stmt.t =
  Utils.debugf ~section 3 "@[<2>transform @{<cyan>statement@}@ `@[%a@]`@]"
    (fun k->k PStmt.print st);
  let info = Stmt.info st in
  match Stmt.view st with
    | Stmt.Decl (id,ty,attrs) ->
      let ty = transform_ty state ~top:true ty in
      Stmt.decl ~info ~attrs id ty
    | _ ->
      (* NOTE: maybe not robust if there are [copy] types *)
      Stmt.map_bind Var.Subst.empty st
        ~bind:(rename_var state)
        ~term:(transform_term state)
        ~ty:(fun _ -> transform_ty state ~top:true)

let transform_problem pb =
  let sigma = Problem.signature pb in
  let state = create_state ~sigma () in
  let pb' =
    Problem.flat_map_statements pb
      ~f:(fun st ->
        let st' = transform_statement state st in
        (* insert additional declarations, the first time [pseudo-prop]
           is used *)
        let other_decls =
          if state.needed && not state.declared
          then declare_ state else []
        in
        other_decls @ [st'])
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
    | TI.Const id, _ when ID.equal id state.true_ -> U.true_
    | TI.Const id, _ when ID.equal id state.false_ -> U.false_
    | TI.Const id, _ when ID.equal id state.pseudo_prop -> U.ty_prop
    | TI.Const id, Some rw when ID.equal id rw.rw_true -> U.true_
    | TI.Const id, Some rw when ID.equal id rw.rw_false -> U.false_
    | _ ->
      U.map () t
        ~bind:(fun () v -> (), v)
        ~f:(fun () -> aux)
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

let pipe_with ~decode ~print ~check =
  let on_encoded =
    Utils.singleton_if print () ~f:(fun () ->
      let module PPb = Problem.Print(P)(P) in
      Format.printf "@[<v2>@{<Yellow>after %s@}: %a@]@." name PPb.print)
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
           If_then_else, Present; HOF, Absent])
    ~map_spec:Transform.Features.(update Prop_args Absent)
    ~on_encoded
    ~encode:transform_problem
    ~decode
    ()

let pipe ~print ~check =
  let decode state = Problem.Res.map_m ~f:(decode_model state) in
  pipe_with ~decode ~print ~check
