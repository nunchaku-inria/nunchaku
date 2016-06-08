
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Encoding of Datatypes} *)

open Nunchaku_core

module TI = TermInner
module Subst = Var.Subst
module Stmt = Statement
module T = TermInner.Default
module U = T.U
module P = T.P
module PStmt = Stmt.Print(P)(P)


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

type ty = T.t

(* the constructions to encode *)
type to_encode =
  | Test of ID.t
  | Select of ID.t * int
  | Axiom_rec (* recursive function used for eq_corec/acyclicity axioms *)
  | Const of ID.t

let equal_to_encode a b = match a, b with
  | Test a, Test b
  | Const a, Const b -> ID.equal a b
  | Select (a,i), Select (b,j) -> i=j && ID.equal a b
  | Axiom_rec, Axiom_rec -> true
  | Test _, _ | Const _, _ | Select _, _ | Axiom_rec, _ -> false

let hash_to_encode = function
  | Test a -> Hashtbl.hash (ID.hash a, "test")
  | Select (a,i) -> Hashtbl.hash (ID.hash a, "select", i)
  | Axiom_rec -> Hashtbl.hash "axiom_rec"
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
  decode: to_encode ID.Tbl.t;
    (* map translated symbols (cstor/select) to original symbols *)
  tys: encoded_ty ID.Tbl.t;
    (* (co)data -> its encoding *)
  map: ID.t Tbl.t;
    (* map constructors to be encoded, into fresh identifiers *)
}

type decode_state = state

let create_state() = {
  decode=ID.Tbl.create 16;
  tys=ID.Tbl.create 16;
  map=Tbl.create 16;
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
  ID.Tbl.add state.decode id k;
  ()

(* create new IDs for selectors, testers, etc., add them to [state],
   and return a [encoded_ty] *)
let ety_of_dataty state ty =
  let open Stmt in
  assert (ty.ty_vars=[] && U.ty_is_Type ty.ty_type);
  add_ state (Const ty.ty_id) ty.ty_id;
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
  let res = { ety_id=ty.ty_id; ety_cstors } in
  ID.Tbl.replace state.tys ty.ty_id res;
  res

let app_id id l = U.app (U.const id) l
let app_id_fst (id,_) l = app_id id l

(* declare the new constants *)
let common_decls etys =
  let mk_decl (id,ty) =
    Stmt.decl ~info:Stmt.info_default ~attrs:[] id ty
  in
  let tys =
    List.map (fun ety -> mk_decl (ety.ety_id,U.ty_type)) etys
  in
  let others =
    CCList.flat_map
      (fun ety ->
         CCList.flat_map
           (fun ec ->
              mk_decl ec.ecstor_cstor
              :: mk_decl ec.ecstor_test
              :: List.map mk_decl ec.ecstor_proj)
           ety.ety_cstors)
      etys
  in
  List.rev_append tys others

let common_axioms etys =
  let mk_ax f = Stmt.axiom1 ~info:Stmt.info_default f in
  (* axiomatize new constants *)
  CCList.flat_map
    (fun ety ->
       (* define projectors *)
       let x = Var.makef ~ty:(U.const ety.ety_id) "v_%a" ID.print_name ety.ety_id in
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
              let proj_ty_arg ty = match U.ty_unfold ty with
                | _, [_], ret -> ret
                | _ -> assert false
              in
              let mk_vars c =
                List.mapi
                  (fun i (_,ty) -> Var.makef ~ty:(proj_ty_arg ty) "l_%d" i)
                  c.ecstor_proj
              in
              let vars1 = mk_vars c1 in
              let vars2 = mk_vars c2 in
              U.forall_l
                (vars1 @ vars2)
                (U.neq
                   (app_id_fst c1.ecstor_cstor (List.map U.var vars1))
                   (app_id_fst c2.ecstor_cstor (List.map U.var vars2)))
              |> mk_ax)
       (* injectivity for each constructor [c]:
          [forall a1...an b1...bn.
            c(a1...an) = c(b1...bn) => a1=b1 & ... & an=bn]
       *)
       and ax_injectivity =
         CCList.filter_map
           (fun ec ->
              let c_id, c_ty = ec.ecstor_cstor in
              let _, args, _ = U.ty_unfold c_ty in
              if args=[] then None
              else (
                let vars1 = List.mapi (fun i ty -> Var.makef ~ty "x_%d" i) args
                and vars2 = List.mapi (fun i ty -> Var.makef ~ty "y_%d" i) args
                in
                U.forall_l (vars1 @ vars2)
                  (U.imply
                     (U.eq
                        (U.app_const c_id (List.map U.var vars1))
                        (U.app_const c_id (List.map U.var vars2)))
                     (U.and_
                        (List.map2
                           (fun v1 v2 -> U.eq (U.var v1) (U.var v2))
                           vars1 vars2)))
                |> mk_ax
                |> CCOpt.return
              ))
           ety.ety_cstors
       in
       ax_exhaustiveness :: ax_injectivity @ ax_projs @ ax_disjointness
    )
    etys

(* acyclicity of datatypes:
   - declare a recursive fun [occurs_in : ty -> ty -> prop] such that
     [occurs_in a b] is true iff [a] is a strict subterm of [b].
   - then, assert [forall a. not (occurs_in a a)]
*)
let acyclicity_ax state ety =
  let id = ety.ety_id in
  (* is [ty = id]? *)
  let is_same_ty ty = match T.repr ty with
    | TI.Const id' -> ID.equal id id'
    | _ -> false
  in
  (* [id_c : id -> id -> prop] *)
  let id_c = ID.make_f "occurs_in_%a" ID.print_name id in
  let ty_c = U.ty_arrow_l [U.const id; U.const id] U.ty_prop in
  let def_c = Stmt.mk_defined id_c ty_c in
  ID.Tbl.add state.decode id_c Axiom_rec;
  (* definition:
     [occurs_in x y :=
       exists cstor.
       (y = cstor a1...an && (Or_k (x=a_k || occurs_in x a_k)))]
  *)
  let x = Var.make ~ty:(U.const id) ~name:"x" in
  let y = Var.make ~ty:(U.const id) ~name:"y" in
  let vars = [x;y] in
  let ax_c =
    List.map
      (fun cstor ->
         (* guard: [is_cstor y] *)
         let test = U.app_const (fst cstor.ecstor_test) [U.var y] in
         let subcases =
           CCList.flat_map
             (fun (proj,proj_ty) -> match U.ty_unfold proj_ty with
                | _, [_], ret when is_same_ty ret ->
                  (* this is a recursive argument, hence a possible case *)
                  [ U.eq (U.var x) (U.app_const proj [U.var y])
                  ; U.app_const id_c [U.var x; U.app_const proj [U.var y]]
                  ]
                | _ -> [])
             cstor.ecstor_proj
         in
         U.and_ [test; U.or_ subcases])
      ety.ety_cstors
    |> U.or_
  in
  let def_c =
    Stmt.axiom_rec ~info:Stmt.info_default
      [ { Stmt.rec_defined=def_c;
          rec_vars=vars;
          rec_eqns=Stmt.Eqn_single (vars, ax_c)
        } ]
  in
  (* also assert [forall x y. not (occurs_in x x)] *)
  let ax_no_cycle =
    let a = Var.make ~ty:(U.const id) ~name:"a" in
    U.forall a
      (U.not_ (U.app_const id_c [U.var a; U.var a]))
  in
  [ def_c
  ; Stmt.axiom1 ~info:Stmt.info_default ax_no_cycle
  ]

(* encode list of data into axioms *)
let encode_data state l =
  let etys = List.map (ety_of_dataty state) l in
  let decl_l = common_decls etys in
  let ax_l = common_axioms etys in
  let acyclicity_l = CCList.flat_map (acyclicity_ax state) etys in
  decl_l @ acyclicity_l @ ax_l

(* axiomatization of equality of codatatypes:
  - declare a recursive fun [eq_corec : ty -> ty -> prop] such that
    [eq_corec a b] is true iff [a] and [b] are structurally equal
   - assert [forall a b. eq_corec a b <=> a=b] *)
let eq_corec_axiom state ety =
  let id = ety.ety_id in
  (* is [ty = id]? *)
  let is_same_ty ty = match T.repr ty with
    | TI.Const id' -> ID.equal id id'
    | _ -> false
  in
  (* [id_c : id -> id -> prop] *)
  let id_c = ID.make_f "eq_corec_%a" ID.print_name id in
  let ty_c = U.ty_arrow_l [U.const id; U.const id] U.ty_prop in
  let def_c = Stmt.mk_defined id_c ty_c in
  ID.Tbl.add state.decode id_c Axiom_rec;
  (* definition:
     [eq_corec x y :=
       exists cstor.
       (x = cstor a1...an && y = cstor b1...bn &&
          And_k eq_corec a_k b_k)]
  *)
  let x = Var.make ~ty:(U.const id) ~name:"x" in
  let y = Var.make ~ty:(U.const id) ~name:"y" in
  let vars = [x;y] in
  let ax_c =
    List.map
      (fun cstor ->
         (* guards: [is_cstor {x,y}] *)
         let test_x = U.app_const (fst cstor.ecstor_test) [U.var x] in
         let test_y = U.app_const (fst cstor.ecstor_test) [U.var y] in
         let subcases =
           List.map
             (fun (proj,proj_ty) ->
                (* how do we decide whether the arguments are equal? *)
                let mk_eq = match U.ty_unfold proj_ty with
                  | _, [_], ret when is_same_ty ret ->
                    (fun a b -> U.app_const id_c [a; b])
                  | _ -> U.eq
                in
                mk_eq (U.app_const proj [U.var x]) (U.app_const proj [U.var y])
             )
             cstor.ecstor_proj
         in
         U.and_ (test_x :: test_y :: subcases))
      ety.ety_cstors
    |> U.or_
  in
  let def_c =
    Stmt.axiom_rec ~info:Stmt.info_default
      [ { Stmt.rec_defined=def_c;
          rec_vars=vars;
          rec_eqns=Stmt.Eqn_single (vars, ax_c)
        } ]
  in
  (* also assert [forall x y. x=y <=> eq_corec x y] *)
  let ax_eq =
    let x = Var.make ~ty:(U.const id) ~name:"x" in
    let y = Var.make ~ty:(U.const id) ~name:"y" in
    U.forall_l [x;y]
      (U.eq
         (U.eq (U.var x) (U.var y))
         (U.app_const id_c [U.var x; U.var y]))
  in
  [ def_c
  ; Stmt.axiom1 ~info:Stmt.info_default ax_eq
  ]

(* encode list of codata into axioms *)
let encode_codata state l =
  let etys = List.map (ety_of_dataty state) l in
  let decl_l = common_decls etys in
  let ax_l = common_axioms etys in
  (* definition of coinductive equality *)
  let eq_axiom_l = CCList.flat_map (eq_corec_axiom state) etys in
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
  pb', state

(** {2 Decoding} *)

(* TODO: decode terms using values of Nil and Cons *)

type fun_def = T.t Var.t list * (T.t, T.t) Model.DT.t * Model.symbol_kind

module IntMap = CCMap.Make(CCInt)

(* temporary structure used for decoding terms *)
type decoding = {
  dec_constants: (encoded_ty * T.t option ref) ID.Map.t;
    (* set of constants whose type is a (co)data, and therefore
       that are to be removed by decoding.
       Each constant maps to the corresponding {!encoded_ty}, and possibly
       its cached value *)
  dec_test: fun_def ID.Map.t;
    (* tester -> definition of tester *)
  dec_select: fun_def IntMap.t ID.Map.t;
    (* cstor, definition of selectors *)
}

let decoding_empty = {
  dec_constants=ID.Map.empty;
  dec_test=ID.Map.empty;
  dec_select=ID.Map.empty
}

(* build a {!decoding} structure from the model *)
let build_decoding state m =
  Model.fold
    decoding_empty
    m
    ~finite_types:(fun dec (ty,dom) ->
      match T.repr ty with
        | TI.Const id when ID.Tbl.mem state.tys id ->
          (* [id] is a (co)data, and we know its encoding *)
          let ety = ID.Tbl.find state.tys id in
          List.fold_left
            (fun dec c ->
               let dec_constants = ID.Map.add c (ety,ref None) dec.dec_constants in
               {dec with dec_constants;})
            dec dom
        | _ -> dec)
    ~funs:(fun dec (t,vars,dt,k) -> match T.repr t with
      | TI.Const id ->
        begin match ID.Tbl.get state.decode id with
          | None -> dec
          | Some (Test _) ->
            {dec with dec_test=ID.Map.add id (vars,dt,k) dec.dec_test}
          | Some (Select (c,i)) ->
            let m = ID.Map.get_or ~or_:IntMap.empty c dec.dec_select in
            let m = IntMap.add i (vars,dt,k) m in
            {dec with dec_select=ID.Map.add c m dec.dec_select}
          | Some (Const _ | Axiom_rec) -> dec
        end
      | _ -> dec)

module DTU = Model.DT_util(T)

let eval_fundef (f:fun_def) (args:T.t list) : T.t =
  let vars, dt, _ = f in
  assert (List.length vars = List.length args);
  let subst = Var.Subst.empty in
  let subst = Var.Subst.add_list ~subst vars args in
  DTU.eval ~subst dt

(* evaluate a boolean function def *)
let eval_bool_fundef (f:fun_def) (args:T.t list) : bool option =
  let _, _, k = f in
  assert (k = Model.Symbol_prop);
  let res = eval_fundef f args in
  match T.repr res with
    | TI.Builtin `True -> Some true
    | TI.Builtin `False -> Some false
    | _ -> None

let find_test_ dec id =
  try ID.Map.find id dec.dec_test
  with Not_found ->
    errorf "could not find, in model,@ the value for tester `%a`" ID.print id

let find_select_ dec c i =
  try
    let map = ID.Map.find c dec.dec_select in
    IntMap.find i map
  with Not_found ->
    errorf "could not find, in model,@ the value for %d-th selector of `%a`"
      i ID.print c

(* FIXME: detect looping constructs (i.e. cyclic codata).
   -> maybe by partial memoization (put a variable + bool ref in the memo table) *)

(* decode a term, recursively, replacing constants of uninterpreted
   domains by their value in the model *)
let decode_term dec t =
  let rec aux t = match T.repr t with
    | TI.Const id ->
      begin match ID.Map.get id dec.dec_constants with
        | None -> t
        | Some (ety,r) ->
          begin match !r with
            | Some t' -> t'
            | None ->
              (* [t] is something like [list_5], and we need to find which
                 constructor it actually is *)
              Utils.debugf ~section 5
                "@[<2>constant `%a`@ corresponds to (co)data `%a`@]"
                (fun k->k ID.print id ID.print ety.ety_id);
              (* find which constructor corresponds to [t] *)
              let ecstor =
                try
                  CCList.find_pred_exn
                    (fun ecstor ->
                       let fundef = find_test_ dec (fst ecstor.ecstor_test) in
                       match eval_bool_fundef fundef [t] with
                         | None ->
                           errorf "cannot evaluate whether `%a`@ \
                                   starts with constructor `%a`"
                             P.print t ID.print (fst ecstor.ecstor_cstor)
                         | Some b -> b)
                    ety.ety_cstors
                with Not_found ->
                  errorf "no constructor corresponds to `%a`" P.print t
              in
              (* evaluate the arguments to this constructor *)
              let cstor = fst ecstor.ecstor_cstor in
              let args =
                List.mapi
                  (fun i _ ->
                     let fundef = find_select_ dec cstor i in
                     let arg = eval_fundef fundef [t] in
                     aux arg)
                  ecstor.ecstor_proj
              in
              let t' = U.app_const cstor args in
              Utils.debugf ~section 5 "@[<2>term `@[%a@]`@ is decoded into `@[%a@]`@]"
                (fun k->k P.print t P.print t');
              (* memoize result *)
              r := Some t';
              t'
          end
      end
    | _ ->
      U.map () t
        ~bind:(fun () v -> (), v)
        ~f:(fun () t -> aux t)
  in
  aux t

(* remove model of constructors/inductive types *)
let decode_model state (m:(_,_) Model.t) : (_,_) Model.t =
  let dec = build_decoding state m in
  let tr_term t = decode_term dec t in
  Model.filter_map m
    ~finite_types:(fun ((ty,_) as tup) ->
      match T.repr ty with
        | TI.Const id when ID.Tbl.mem state.tys id ->
          None (* drop (co)data domains from model *)
        | _ -> Some tup)
    ~constants:(fun (t,u,k) ->
      match T.repr t with
        | TI.Const id when ID.Tbl.mem state.decode id ->
          None (* drop the domain constants *)
        | _ ->
          let t = tr_term t in
          let u = tr_term u in
          Some (t,u,k))
    ~funs:(fun (f,vars,dt,k) -> match T.repr f with
      | TI.Const id when ID.Tbl.mem state.decode id -> None
      | _ ->
        let f = tr_term f in
        let dt = Model.DT.map dt ~term:tr_term ~ty:tr_term in
        Some (f,vars,dt,k))

(** {2 Pipeline} *)

let pipe_with ?on_decoded ~decode ~print ~check =
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
    ?on_decoded
    ~encode:transform_pb
    ~decode
    ()

let pipe ~print ~check =
  let on_decoded = if print
    then
      [Format.printf "@[<2>@{<Yellow>res after %s@}:@ %a@]@."
         name (Problem.Res.print P.print' P.print)]
    else []
  in
  let decode state = Problem.Res.map_m ~f:(decode_model state) in
  pipe_with ~on_decoded ~check ~decode ~print
