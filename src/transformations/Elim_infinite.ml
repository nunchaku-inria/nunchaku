
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Eliminate Infinite Types} *)

open Nunchaku_core

module TI = TermInner
module Subst = Var.Subst
module Stmt = Statement
module Pol = Polarity
module T = TI.Default
module P = T.P
module U = T.U

type term = TermInner.Default.t
type ('a,'b,'c) inv = < eqn : 'a; ind_preds : 'b; ty : 'c >

let name = "elim_infinite"
let section = Utils.Section.make name

exception Error of string

let () = Printexc.register_printer
  (function
    | Error msg -> Some (Utils.err_sprintf "%s:@ %s" name msg)
    | _ -> None)

let fail_ msg = raise (Error msg)
let failf msg = Utils.exn_ksprintf ~f:fail_ msg

type decode_state = unit

type state = {
  to_approx: ID.t option ID.Map.t; (* infinite type -> its approximation *)
  upcast: ID.Set.t; (* upcast functions *)
  mutable incomplete: bool; (* approximation? *)
}

let has_infinite_attr_ =
  List.exists (function Stmt.Attr_infinite -> true | _ -> false)

let has_upcast_attr_ =
  List.exists (function Stmt.Attr_infinite_upcast -> true | _ -> false)

let as_approx_attr_ =
  CCList.find_map
    (function
      | Stmt.Attr_finite_approx id -> Some id
      | _ -> None)

(* find the universal types, build a map "infinite type -> approx" *)
let find_types_st (map,set) st = match Stmt.view st with
  | Stmt.Decl (id, ty, attrs) when U.ty_is_Type ty && has_infinite_attr_ attrs ->
    ID.Map.add id None map, set
  | Stmt.Decl (id, _, attrs) when has_upcast_attr_ attrs ->
    map, ID.Set.add id set
  | Stmt.Decl (id, ty, attrs) when U.ty_is_Type ty ->
    begin match as_approx_attr_ attrs with
      | None -> map, set
      | Some id' ->
        begin match ID.Map.get id' map with
          | None -> failf "could not find infinite type `%a`" ID.print id'
          | Some None -> ID.Map.add id' (Some id) map, set
          | Some (Some id'') ->
            failf "cannot have two approximations `%a` and `%a` for `%a`"
              ID.print id ID.print id'' ID.print id'
        end
    end
  | _ -> map, set

(* is this an infinite type? *)
let ty_is_infinite_ st ty = match T.repr ty with
  | TI.Const id when ID.Map.mem id st.to_approx -> true
  | _ -> false

let declare_incomplete_ st =
  if not st.incomplete then (
    Utils.debug ~section 1 "translation is incomplete";
    st.incomplete <- true;
  )

(* FIXME: stronger criterion for quantifiers (types with infinite card,
   not just the infinite atomic type) *)

let is_upcast_ st t = match T.repr t with
  | TI.Const id -> ID.Set.mem id st.upcast
  | _ -> false

(* encode term: replace all references to universal types by their
   approximation; *)
let rec encode_term st subst pol t = match T.repr t with
  | TI.Var v ->
    begin match Subst.find ~subst v with
      | Some v' -> U.var v'
      | None -> failf "scoping error for `%a`" Var.print_full v
    end
  | TI.Const id ->
    begin match ID.Map.get id st.to_approx with
      | None -> t
      | Some None ->
        (* TODO: introduce a new approximation? *)
        failf "universal type `@[%a@]`@ does not have an approximation" ID.print id
      | Some (Some id') -> U.const id'
    end
  | TI.Bind (`Forall, v, _)
    when ty_is_infinite_ st (Var.ty v) && (pol = Pol.Pos || pol = Pol.NoPol) ->
    (* quantification on infinite type: false *)
    declare_incomplete_ st;
    U.false_ (* TODO: warning? *)
  | TI.Bind (`Exists, v, _)
    when ty_is_infinite_ st (Var.ty v) && (pol = Pol.Neg || pol = Pol.NoPol) ->
    declare_incomplete_ st;
    U.false_
  | TI.App (f, [x]) when is_upcast_ st f ->
    (* erase the "upcast" operator, because it becomes id *)
    encode_term st subst pol x
  | _ ->
    U.map_pol subst pol t
      ~bind:(bind_var st)
      ~f:(encode_term st)

and bind_var st subst v =
  let v' =
    Var.update_ty ~f:(encode_term st subst Pol.NoPol) v
    |> Var.fresh_copy
  in
  let subst = Subst.add ~subst v v' in
  subst, v'

let encode_statement map st = match Stmt.view st with
  | Stmt.Decl (_, ty, attrs) when has_infinite_attr_ attrs ->
    assert (U.ty_is_Type ty);
    [] (* remove infinite type *)
  | Stmt.Decl (_, _, attrs) when has_upcast_attr_ attrs ->
    [] (* remove upcast functions *)
  | _ ->
    let tr_term subst t = encode_term map subst Pol.Pos t in
    let tr_ty subst ty = encode_term map subst Pol.NoPol ty in
    let st' =
      Stmt.map_bind
        Subst.empty st
        ~bind:Subst.rename_var ~term:tr_term ~ty:tr_ty
    in
    [st']

let encode_pb pb =
  let to_approx, set =
    CCVector.fold find_types_st (ID.Map.empty,ID.Set.empty)
      (Problem.statements pb)
  in
  let st = {to_approx; upcast=set; incomplete=false; } in
  let pb' =
    Problem.flat_map_statements pb ~f:(encode_statement st)
  in
  (* might have lost completeness *)
  if st.incomplete
  then Problem.set_sat_means_unknown pb'
  else pb'

(* TODO: decoding (i.e. return a model for infinite types)? *)

let pipe_with ~decode ~print ~check =
  let on_encoded =
    Utils.singleton_if print ()
      ~f:(fun () ->
        let module PPb = Problem.Print(P)(P) in
        Format.printf "@[<v2>@{<Yellow>after %s@}: %a@]@." name PPb.print)
    @
    Utils.singleton_if check ()
      ~f:(fun () ->
        let module C = TypeCheck.Make(T) in
        C.check_problem ?env:None)
  in
  Transform.make
    ~on_encoded
    ~name
    ~encode:(fun p -> encode_pb p, ())
    ~decode
    ()

let pipe ~print ~check =
  let decode () res = res in
  pipe_with ~print ~decode ~check
