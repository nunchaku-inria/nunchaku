
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

type inv = <ind_preds:[`Absent]; ty:[`Mono]; eqn:[`Absent]>

type term = T.t
type ty = T.t
type problem = (term, ty, inv) Problem.t
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
  mutable declared: bool;
  mutable needed: bool;
}

let create_state ~sigma () =
  { true_ = ID.make "true_";
    false_ = ID.make "false_";
    pseudo_prop = ID.make "prop_";
    declared = false;
    needed = false;
    sigma;
  }

(* statements that declare the pseudo-prop type *)
let declare_ state : (_,_,_) Stmt.t list =
  assert (not state.declared);
  state.declared <- true;
  let mk_decl id ty =
    Stmt.decl ~info:Stmt.info_default ~attrs:[] id ty
  in
  let decl_ty = mk_decl state.pseudo_prop (U.ty_builtin `Type)
  and decl_true = mk_decl state.true_ (U.ty_const state.pseudo_prop)
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

(* rename [v], and maybe update its type from [prop] to [pseudo_prop] *)
and transform_var state v =
  let v' = Var.fresh_copy v in
  Var.update_ty v'
    ~f:(transform_ty state ~top:true)

let rename_var state subst v =
  let v' = transform_var state v in
  Var.Subst.add ~subst v v', v'

(* traverse a term, replacing any argument [a : prop]
   with [if a then pseudo_true else pseudo_false];
   also, change variables' types *)
let transform_term state subst t =
  let rec aux subst t = match T.repr t with
    | TI.Var v -> U.var (Var.Subst.find_exn ~subst v)
    | TI.App (f, l) ->
      let ty_f = find_ty state f in
      let _, ty_args, _ = U.ty_unfold ty_f in
      (* translate head and arguments *)
      let f' = aux subst f in
      let l' = List.map (aux subst) l in
      assert (List.length l' = List.length ty_args);
      (* adjust types: if some argument is a [prop], insert a "ite" *)
      let l' =
        List.map2
          (fun arg ty ->
             if U.ty_is_Prop ty
             then (
               state.needed <- true;
               U.ite arg (U.const state.true_) (U.const state.false_)
             ) else arg)
          l'
          ty_args
      in
      U.app f' l'
    | _ ->
      U.map subst t
        ~bind:(rename_var state) ~f:aux
  in
  aux subst t

let transform_statement state st : (_,_,_) Stmt.t =
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

let decode_model state m =
  m (* TODO *)

(* TODO: require the spec "type:mono, ite:present; hof: absent" *)

let pipe_with ~decode ~print ~check =
  let on_encoded =
    Utils.singleton_if print () ~f:(fun () ->
      let module PPb = Problem.Print(P)(P) in
      Format.printf "@[<v2>@{<Yellow>after %s@}: %a@]@." name PPb.print)
    @
    Utils.singleton_if check ()
      ~f:(fun () ->
         let module C = TypeCheck.Make(T) in
         C.check_problem ?env:None)
  in
  Transform.make
    ~name
    ~on_encoded
    ~encode:transform_problem
    ~decode
    ()

let pipe ~print ~check =
  let decode state = Problem.Res.map_m ~f:(decode_model state) in
  pipe_with ~decode ~print ~check
