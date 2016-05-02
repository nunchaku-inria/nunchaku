
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Encoding of Datatypes}

     encode (co)datatypes.
     a [data a =  c1 x1 | ... | cn xn] becomes a type [a]
     plus axioms defining each constructor, selector and tester. *)

open Nunchaku_core

module TI = TermInner
module Subst = Var.Subst
module Stmt = Statement

(* TODO: require elimination of pattern matching earlier, in types *)

type inv = <ty:[`Mono]; ind_preds:[`Absent]; eqn:[`Single]>

let name = "elim_data"
let section = Utils.Section.make name

exception Error of string

let () = Printexc.register_printer
    (function
      | Error msg -> Some (Utils.err_sprintf "@[elim_(co)data:@ %s@]" msg)
      | _ -> None)

let error msg = raise (Error msg)
let errorf msg = Utils.exn_ksprintf ~f:error msg

module type S = sig
  module T : TI.S

  type decode_state

  val transform_pb :
    (T.t, T.t, inv) Problem.t ->
    (T.t, T.t, inv) Problem.t * decode_state

  val decode_model :
    decode_state -> (T.t, T.t) Model.t -> (T.t, T.t) Model.t

  val pipe :
    print:bool ->
    check:bool ->
    ((T.t,T.t, inv) Problem.t,
     (T.t,T.t, inv) Problem.t,
      (T.t,T.t) Problem.Res.t, (T.t,T.t) Problem.Res.t
    ) Transform.t

  val pipe_with :
    decode:(decode_state -> 'c -> 'd) ->
    print:bool ->
    check:bool ->
    ((T.t,T.t, inv) Problem.t,
     (T.t,T.t, inv) Problem.t, 'c, 'd
    ) Transform.t
end

module Make
(T : TI.S)
: S with module T = T
= struct
  module T = T
  module U = TI.Util(T)
  module P = TI.Print(T)
  module PStmt = Stmt.Print(P)(P)

  type ty = T.t

  (* the constructions to encode *)
  type to_encode =
    | Test of ID.t
    | Select of ID.t * int
    | Const of ID.t

  type decode_state = {
    ds_data : unit ID.Tbl.t;
      (* set of identifiers corresponding to datatypes *)
    ds_rev_map : to_encode ID.Tbl.t;
      (* map translated symbols to original symbols *)
  }

  let create_decode_state () =
    { ds_data=ID.Tbl.create 16;
      ds_rev_map=ID.Tbl.create 16;
    }

  let equal_to_encode a b = match a, b with
    | Test a, Test b
    | Const a, Const b -> ID.equal a b
    | Select (a,i), Select (b,j) -> i=j && ID.equal a b
    | Test _, _ | Const _, _ | Select _, _ -> false

  let hash_to_encode = function
    | Test a -> Hashtbl.hash (ID.hash a, "test")
    | Select (a,i) -> Hashtbl.hash (ID.hash a, "select", i)
    | Const a -> Hashtbl.hash (ID.hash a, "const")

  module Tbl = CCHashtbl.Make(struct
      type t = to_encode
      let equal = equal_to_encode
      let hash = hash_to_encode
    end)

  type encoded_cstor = {
    ecstor_cstor: (ID.t * ty);
    ecstor_test: (ID.t * ty);
    ecstor_proj: (ID.t * ty) list;
  }

  (* encoded type *)
  type encoded_ty = {
    ety_id: ID.t;
    ety_cstors: encoded_cstor list;
  }

  type state = {
    decode: decode_state;
    map: ID.t Tbl.t;
      (* map constructors to be encoded, into fresh identifiers *)
  }

  let create_state() = {
    decode=create_decode_state();
    map=Tbl.create 64;
  }

  let rec tr_term state t = match T.repr t with
    | TI.Const id ->
      Tbl.get_or state.map (Const id) ~or_:id |> U.const
    | TI.Builtin (`DataSelect (id,i)) ->
      begin match Tbl.get state.map (Select(id,i)) with
        | None -> t
        | Some id' -> U.const id'
      end
    | TI.Builtin (`DataTest id) ->
      begin match Tbl.get state.map (Test id) with
        | None -> t
        | Some id' -> U.const id'
      end
    | TI.Match _ ->
      errorf "expected pattern-matching to be encoded,@ got `@[%a@]`" P.print t
    | _ ->
      U.map () t
        ~bind:(fun () v -> (), v)
        ~f:(fun () -> tr_term state)

  let tr_ty = tr_term

  (* add binding to state *)
  let add_ state k id =
    Tbl.add state.map k id;
    ID.Tbl.add state.decode.ds_rev_map id k;
    ()

  (* create new IDs for selectors, testers, etc., add them to [state],
     and return a [encoded_ty] *)
  let ety_of_dataty state ty =
    let open Stmt in
    assert (ty.ty_vars=[]);
    add_ state (Const ty.ty_id) ty.ty_id;
    ID.Tbl.add state.decode.ds_data ty.ty_id ();
    (* add destructors, testers, constructors *)
    let ety_cstors = ID.Map.fold
        (fun _ cstor acc ->
           let c_id = cstor.cstor_name in
           add_ state (Const c_id) c_id;
           let test = ID.make_f "is_%a" ID.print_name c_id in
           let ty_test = U.ty_arrow (U.const ty.ty_id) U.ty_prop in
           add_ state (Test c_id) test;
           let selectors =
             List.mapi
               (fun i ty_arg ->
                  let s = ID.make_f "select_%a_%d" ID.print_name c_id i in
                  let ty_s = U.ty_arrow (U.const ty.ty_id) ty_arg in
                  add_ state (Select (c_id, i)) s;
                  s, ty_s)
               cstor.cstor_args
           in
           { ecstor_proj=selectors;
             ecstor_test=(test, ty_test);
             ecstor_cstor=(c_id, cstor.cstor_type)} :: acc)
        ty.ty_cstors []
    in
    { ety_id=ty.ty_id; ety_cstors }

  let app_id id l = U.app (U.const id) l
  let app_id_fst (id,_) l = app_id id l
  let var_f ~ty f = CCFormat.ksprintf f ~f:(fun name -> Var.make ~ty ~name)

  (* declare the new constants *)
  let common_decls etys =
    let mk_decl (id,ty) = Stmt.ty_decl ~info:Stmt.info_default ~attrs:[] id ty in
    CCList.flat_map
      (fun ety ->
         mk_decl (ety.ety_id,U.ty_type)
         :: CCList.flat_map
             (fun ec ->
                mk_decl ec.ecstor_cstor
                :: mk_decl ec.ecstor_test
                :: List.map mk_decl ec.ecstor_proj)
             ety.ety_cstors)
      etys

  let common_axioms etys =
    let mk_ax f = Stmt.axiom1 ~info:Stmt.info_default f in
    (* axiomatize new constants *)
    CCList.flat_map
      (fun ety ->
         (* define projectors *)
         let x = var_f ~ty:(U.const ety.ety_id) "v_%a" ID.print_name ety.ety_id in
         (* [forall x, is_c x => x = c (select_c_1 x) ... (select_c_n x)] *)
         let ax_projs =
           List.map
             (fun ec ->
                U.forall x
                  (U.imply
                     (app_id_fst ec.ecstor_test [U.var x])
                     (U.eq (U.var x)
                        (app_id_fst ec.ecstor_cstor
                           (List.map (fun p -> app_id_fst p [U.var x]) ec.ecstor_proj))))
                |> mk_ax)
             ety.ety_cstors
         (* [forall x, Or_c is_c x] *)
         and ax_exhaustiveness =
           U.forall x
             (U.or_
                (List.map
                   (fun ec -> app_id_fst ec.ecstor_test [U.var x])
                   ety.ety_cstors))
           |> mk_ax
         (* [forall x1...xn y1...ym. c1 x1...xn != c2 y1...ym] *)
         and ax_disjointness =
           CCList.diagonal ety.ety_cstors
           |> List.map
             (fun (c1,c2) ->
                let vars1 = List.mapi (fun i (_,ty) -> var_f ~ty "l_%d" i) c1.ecstor_proj in
                let vars2 = List.mapi (fun i (_,ty) -> var_f ~ty "r_%d" i) c2.ecstor_proj in
                U.forall_l
                  (vars1 @ vars2)
                  (U.neq
                     (app_id_fst c1.ecstor_cstor (List.map U.var vars1))
                     (app_id_fst c2.ecstor_cstor (List.map U.var vars2)))
                |> mk_ax)
         in
         ax_exhaustiveness :: ax_projs @ ax_disjointness
      )
      etys

  (* acyclicity of datatypes:
     - declare a recursive pred [contains : ty -> ty -> prop] such that
       [contains a b] is true iff [a] contains [b] (strictly!).
     - then, assert [forall a. not (contains a a)]
  *)
  let acyclicity_ax _ety =
    assert false (* TODO *)

  (* encode list of data into axioms *)
  let encode_data state l =
    let etys = List.map (ety_of_dataty state) l in
    let decl_l = common_decls etys in
    let ax_l = common_axioms etys in
    let acyclicity_l = List.map acyclicity_ax etys in
    decl_l @ acyclicity_l @ ax_l

  (* TODO: axiomatization of equality of codatatypes *)
  let eq_axiom _ety =
    assert false

  (* encode list of codata into axioms *)
  let encode_codata state l =
    let etys = List.map (ety_of_dataty state) l in
    let decl_l = common_decls etys in
    let ax_l = common_axioms etys in
    (* definition of coinductive equality *)
    let eq_axiom_l = List.map eq_axiom etys in
    decl_l @ eq_axiom_l @ ax_l

  let encode_stmt state stmt =
    match Stmt.view stmt with
      | Stmt.TyDef (`Codata, l) ->
        Utils.debugf ~section 2 "@[<2>encode codata@ `@[%a@]`@]"
          (fun k->k PStmt.print_tydefs (`Codata, l));
        encode_codata state l
      | Stmt.TyDef (`Data, l) ->
        Utils.debugf ~section 2 "@[<2>encode data@ `@[%a@]`@]"
          (fun k->k PStmt.print_tydefs (`Data, l));
        encode_data state l
      | _ ->
        let stmt =
          Stmt.map stmt ~term:(tr_term state) ~ty:(tr_ty state)
        in
        [stmt]

  let transform_pb pb =
    let state = create_state () in
    let pb' = Problem.flat_map_statements pb ~f:(encode_stmt state) in
    pb', state.decode

  (* remove model of constructors/inductive types *)
  let decode_model state m =
    Model.filter m
      ~funs:(fun (f,_,_,_) -> match T.repr f with
        | TI.Const id when ID.Tbl.mem state.ds_rev_map id -> false
        | _ -> true)

  let pipe_with ~decode ~print ~check =
    let on_encoded =
      Utils.singleton_if print ()
        ~f:(fun () ->
          let module Ppb = Problem.Print(P)(P) in
          Format.printf "@[<v2>@{<Yellow>after %s@}: %a@]@." name Ppb.print)
      @
      Utils.singleton_if check ()
        ~f:(fun () ->
           let module C = TypeCheck.Make(T) in
           C.check_problem ?env:None)
    in
    Transform.make
      ~name
      ~on_encoded
      ~encode:transform_pb
      ~decode
      ()

  let pipe ~print ~check =
    let decode state = Problem.Res.map_m ~f:(decode_model state) in
    pipe_with ~check ~decode ~print
end
