
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Elimination of Higher-Order Functions} *)

open Nunchaku_core

module TI = TermInner
module Stmt = Statement
module Subst = Var.Subst
module Pol = Polarity
module T = TermInner.Default
module U = T.U
module P = T.P
module PStmt = Stmt.Print(P)(P)
module TM = TermMono.Make(T)
module TMI = TermMono
module TyI = TypeMono
module Ty = TypeMono.Make(T)
module Red = Reduce.Make(T)

let name = "elim_hof"
let section = Utils.Section.make name

let fpf = Format.fprintf

exception Error of string

let () = Printexc.register_printer
  (function
    | Error msg -> Some (Utils.err_sprintf "elim HOF:@ %s" msg)
    | _ -> None)

let error_ msg = raise (Error msg)
let errorf_ msg = CCFormat.ksprintf msg ~f:error_

type term = T.t
type ty = T.t

(** {2 Computing Arities}

    The point here is to find, for every functional value (var/const/select),
    the set of arities it is (partially) applied with.
    Only functions partially applied at least once are of interest
    in this section. *)

module IntSet = CCSet.Make(CCInt)
module IntMap = CCMap.Make(CCInt)

type arity_set = {
  as_set : IntSet.t;
  as_ty_args : ty list; (* shortcut to the type arguments of the function *)
  as_ty_ret : ty; (* shortcut to the return type of the function *)
}

let pp_arity_set out set =
  fpf out "{@[%a@]}" (IntSet.print ~start:"" ~stop:"" CCFormat.int) set.as_set

type fun_ =
  | F_id of ID.t
  | F_var of ty Var.t
  | F_select of ID.t * int (* data-select (id,i) *)

let pp_fun out = function
  | F_id i -> ID.print out i
  | F_var v -> Var.print_full out v
  | F_select (id,i) -> Format.fprintf out "select-%a-%d" ID.print id i

let compare_fun f1 f2 =
  let to_int_ = function F_id _ -> 0 | F_var _ -> 1 | F_select _ -> 2 in
  match f1, f2 with
    | F_id id1, F_id id2 -> ID.compare id1 id2
    | F_var v1, F_var v2 -> Var.compare v1 v2
    | F_select (id1,i1), F_select (id2,i2) ->
      CCOrd.( ID.compare id1 id2 <?> (int_, i1, i2))
    | F_id _, _
    | F_var _, _
    | F_select _, _ -> CCOrd.int_ (to_int_ f1) (to_int_ f2)

module FunMap = CCMap.Make(struct type t = fun_ let compare = compare_fun end)

(* print arity map *)
let pp_arities out tbl =
  let pp_pair out (id,set) = fpf out "@[%a → @[%a@] over %d@]"
    pp_fun id pp_arity_set set (List.length set.as_ty_args)
  in
  fpf out "@[<v>%a@]"
    (CCFormat.seq ~start:"" ~stop:"" ~sep:"" pp_pair)
    (FunMap.to_seq tbl)

(* With [id : ty_args -> ty_ret], report a use of [id] with [n] arguments
   where [n <= List.length ty_args] *)
let add_arity_ m (f:fun_) n ty_args ty_ret : arity_set FunMap.t =
  let set =
    try FunMap.find f m
    with Not_found ->
      { as_set=IntSet.empty;
        as_ty_args=ty_args;
        as_ty_ret=ty_ret;
      }
  in
  let set = {set with as_set=IntSet.add n set.as_set;} in
  FunMap.add f set m

(* is [id] a function symbol? If yes, return its type arguments and return type *)
let as_fun_ ~env id =
  let info = Env.find_exn ~env id in
  match info.Env.def with
  | Env.Fun_def _
  | Env.Fun_spec _
  | Env.Copy_abstract _
  | Env.Copy_concrete _
  | Env.NoDef ->
      let tyvars, args, ret = U.ty_unfold info.Env.ty in
      assert (tyvars=[]); (* mono, see {!inv} *)
      Some (args, ret)
  | Env.Data (_,_,_)
  | Env.Cstor (_,_,_,_) (* always fully applied *)
  | Env.Copy_ty _ -> None
  | Env.Pred (_,_,_,_,_) -> assert false (* see {!inv} *)

let ty_is_ho_ ty =
  let _, args, _ = U.ty_unfold ty in
  List.length args > 0

(* is [v] an higher-order variable? *)
let var_is_ho_ v = ty_is_ho_ (Var.ty v)

let add_arity_var_ m v =
  let tyvars, args, ret = U.ty_unfold (Var.ty v) in
  assert (tyvars=[]); (* mono, see {!inv} *)
  add_arity_ m (F_var v) 0 args ret

let add_arity_select_ m id n ty =
  let tyvars, args, ret = U.ty_unfold ty in
  assert (tyvars=[]); (* mono, see {!inv} *)
  assert (args <> []); (* at least one arg: the datatype *)
  add_arity_ m (F_select (id,n)) 1 args ret

let ty_term_ ~env t = U.ty_exn ~sigma:(Env.find_ty ~env) t

(* compute set of arities for higher-order functions *)
let compute_arities_term ~env m t =
  let m = ref m in
  let rec aux t = match TM.repr t with
    | TMI.Const id ->
        begin match as_fun_ ~env id with
        | Some ([], _)
        | None -> ()  (* constant, just ignore *)
        | Some (ty_args, ty_ret) ->
            (* function that is applied to 0 arguments (e.g. as a parameter) *)
            m := add_arity_ !m (F_id id) 0 ty_args ty_ret
        end
    | TMI.Var v when var_is_ho_ v ->
        (* higher order variable *)
        m := add_arity_var_ !m v
    | TMI.Builtin (`DataSelect (id,n)) ->
        let ty = ty_term_ ~env t in
        m := add_arity_select_ !m id n ty
    | TMI.App (f, l) ->
        assert (l<>[]);
        begin match TM.repr f with
        | TMI.App _ -> assert false
        | TMI.Const id ->
            begin match as_fun_ ~env id with
              | Some ([],_) -> assert false
              | None -> ()   (* not a function *)
              | Some (ty_args, ty_ret) ->
                  assert (List.length ty_args >= List.length l);
                  m := add_arity_ !m (F_id id) (List.length l) ty_args ty_ret
            end;
            (* explore subterms *)
            List.iter aux l
        | TMI.Var v ->
            assert (var_is_ho_ v);
            (* higher order variable applied to [l] *)
            let tyvars, args, ret = U.ty_unfold (Var.ty v) in
            assert (tyvars=[]); (* mono, see {!inv} *)
            assert (List.length args >= List.length l);
            m := add_arity_ !m (F_var v) (List.length l) args ret
        | TMI.Builtin (`DataSelect (id,n)) ->
            let ty = ty_term_ ~env f in
            let tyvars, args, ret = U.ty_unfold ty in
            assert (tyvars=[]); (* mono, see {!inv} *)
            assert (List.length args >= List.length l);
            (* selector applied, and unapplied *)
            m := add_arity_select_ !m id n ty;
            m := add_arity_ !m (F_select (id, n)) (List.length l) args ret
        | _ -> aux_rec t
        end
    | _ -> aux_rec t
  (* recurse *)
  and aux_rec t =
    U.iter () t
      ~f:(fun () t -> aux t)
      ~bind:(fun () v ->
        if var_is_ho_ v then (
          (* higher order variable always has arity 0 *)
          let _, args, ret = U.ty_unfold (Var.ty v) in
          m := add_arity_ !m (F_var v) 0 args ret
        ))
  in
  aux t;
  !m

(* NOTE: we consider that all functions are always totally applied at least
   once, so that the app symbol and extensionality axioms are generated.

   TODO: optim: do not do that if remaining args are guaranteed to be of
   infinite cardinality (extensionality not strictly needed then). Problem
   is for [unit -> unit] and the likes. *)

let compute_arities_stmt ~env m (stmt:(_,_) Stmt.t) =
  let f = compute_arities_term ~env in
  (* declare  that [id : ty] is fully applied *)
  let add_full_arity id ty m =
    let _, args, ret = U.ty_unfold ty in
    let n = List.length args in
    add_arity_ m id n args ret
  (* declare that [id : arg -> ret] is used with arity 1 *)
  and add_arity1 id ty m =
    let _, args, ret = U.ty_unfold ty in
    assert (args <> []);
    add_arity_ m id 1 args ret
  in
  let m = match Stmt.view stmt with
    | Stmt.Axiom (Stmt.Axiom_rec l) ->
        (* function defined with "rec": always consider it fully applied *)
        List.fold_left
          (fun m def ->
            (* declare defined ID with full arity *)
            let id = def.Stmt.rec_defined.Stmt.defined_head in
            let m = add_full_arity (F_id id) def.Stmt.rec_defined.Stmt.defined_ty m in
            (* add arity 0 to higher-order parameter variables *)
            let m = match def.Stmt.rec_eqns with
              | Stmt.Eqn_single (vars,_rhs) ->
                  List.fold_left
                    (fun m v -> if var_is_ho_ v then add_arity_var_ m v else m)
                    m vars
              | _ -> assert false (* by typing *)
            in
            m)
          m l
    | Stmt.Copy c ->
        (* consider the abstract/concrete functions are applied to 1 arg *)
        m
        |> add_full_arity (F_id c.Stmt.copy_abstract) c.Stmt.copy_abstract_ty
        |> add_arity1 (F_id c.Stmt.copy_abstract) c.Stmt.copy_abstract_ty
        |> add_full_arity (F_id c.Stmt.copy_concrete) c.Stmt.copy_concrete_ty
        |> add_arity1 (F_id c.Stmt.copy_concrete) c.Stmt.copy_concrete_ty
    | _ -> m
  in
  Stmt.fold m stmt ~ty:f ~term:f

(* arity set: function always fully applied?
   true iff the set contains exactly [length as_ty_args] *)
let always_fully_applied_ set =
  assert (not (IntSet.is_empty set.as_set));
  let n = List.length set.as_ty_args in
  IntSet.mem n set.as_set && IntSet.cardinal set.as_set = 1

let compute_arities_pb ~env pb =
  let m =
    Problem.statements pb
    |> CCVector.fold (compute_arities_stmt ~env) FunMap.empty
  in
  (* remove functions that are always fully applied *)
  FunMap.filter
    (fun _ set -> not (always_fully_applied_ set))
    m

(** {2 Handle Types}

    A handle type is an abstraction of a function type. For instance,
    given [plus : nat -> (nat -> nat)], where plus is sometimes applied
    to 1 argument and sometimes to two arguments, we:
    - introduce the handle [H] that stands for [nat->nat],
    - declare that [plus : nat -> H],
    - introduce an application symbol [app_H : H -> nat -> nat],
    - replace any term of the form [plus x y] with [app_H (plus x) y],
    - introduce [proto] function(s) [proto_H : H -> nat]
    - axiomatize extensionality for [H]
  *)

type handle =
  | H_leaf of encoded_ty (* leaf type *)
  | H_arrow of encoded_ty * handle (* [H_arrow (a,b)] reifies [a -> b] into an atomic type *)

and encoded_ty = ty

let handle_leaf x = H_leaf x

let rec pp_handle out = function
  | H_leaf ty -> Format.fprintf out "(@[leaf@ `@[%a@]`@])" P.print ty
  | H_arrow (a,b) -> Format.fprintf out "(@[arrow@ `@[%a@]`@ %a@])" P.print a pp_handle b

(** {2 State for Encoding and Decoding} *)

(* application symbol (for partial application) *)
type apply_fun = {
  af_id: ID.t;
  af_ty: term; (* type of the function *)
  af_arity: int; (* shortcut: number of arguments *)
}

type fun_encoding_tower_cell =
  | TC_app of apply_fun (* use this "app" function *)
  | TC_first_param of int (* apply the first parameter (given its arity) *)

(* how to encode a given (partially applied) function:
   for each arity the function [f] uses, map the arity
   to a list of application symbols to use.

   A list [app1, app2, app3] means that [f x y z] will be
   encoded as [app3 (app2 (app1 x) y) z]. *)
type fun_encoding = {
  fe_stack: fun_encoding_tower_cell list IntMap.t; (* tower of functions, never empty *)
  fe_args: ty list; (* type arguments used to return the first handle *)
  fe_ret_handle: handle; (* handle type returned by the function *)
}

type decode_state = {
  dst_app_symbols: unit ID.Tbl.t;
    (* set of application symbols *)
  mutable dst_handle_id: ID.t option;
    (* identifier for reifying "->" in handles *)
  mutable fun_encodings: fun_encoding FunMap.t;
    (* partially applied function/variable -> how to encode it *)
  mutable app_symbols: apply_fun Ty.Map.t;
    (* type -> corresponding apply symbol *)
  mutable dst_gensym: int;
    (* counter for new symbols *)
}

type state = {
  env: (term, ty) Env.t;
    (* environment (to get signatures, etc.) *)
  arities: arity_set FunMap.t;
    (* set of arities for partially applied symbols/variables *)
  mutable app_count: int;
    (* used for generating new names *)
  mutable new_stmts : (term, ty) Stmt.t CCVector.vector;
    (* used for new declarations. [id, type, attribute list] *)
  mutable unsat_means_unknown: bool;
    (* did we have to do some approximation? *)
  decode: decode_state;
    (* bookkeeping for, later, decoding *)
}

let pp_apply_fun out f =
  fpf out "@[<2>%a/%d :@ `@[%a@]`@]" ID.print f.af_id f.af_arity P.print f.af_ty

let pp_sc out = function
  | TC_first_param n -> fpf out "first_param (arity %d)" n
  | TC_app f -> pp_apply_fun out f

let pp_fe_tower out =
  fpf out "[@[<v>%a@]]" (CCFormat.list ~start:"" ~stop:"" ~sep:"" pp_sc)

let pp_fun_encoding out =
  fpf out "[@[<v>%a@]]"
    (IntMap.print ~start:"" ~stop:"" ~sep:"" ~arrow:" -> " CCFormat.int pp_fe_tower)

let create_state ~env arities = {
  env;
  arities;
  app_count=0;
  new_stmts=CCVector.create();
  unsat_means_unknown=false;
  decode={
    dst_app_symbols=ID.Tbl.create 16;
    dst_gensym=0;
    dst_handle_id=None;
    fun_encodings=FunMap.empty;
    app_symbols=Ty.Map.empty;
  };
}

(** {2 Encoding} *)

let get_or_create_handle_id ~state : ID.t lazy_t =
  lazy (match state.decode.dst_handle_id with
  | Some i -> i
  | None ->
      let id = ID.make "to" in
      state.decode.dst_handle_id <- Some id;
      let ty_id = U.ty_arrow_l [U.ty_type; U.ty_type] U.ty_type in
      (* declare the symbol [to : type -> type -> type] *)
      let attrs =
        [ Stmt.Attr_is_handle_cstor
        ; Stmt.Attr_incomplete
        ] in
      let stmt = Stmt.decl ~info:Stmt.info_default ~attrs id ty_id in
      CCVector.push state.new_stmts stmt;
      id
  )

let get_handle_id_decode ~state : ID.t lazy_t =
  match state.dst_handle_id with
    | Some i -> Lazy.from_val i
    | None -> assert false

(* encode a type parameter so it becomes first-order (replace [->] with [to]) *)
let encode_ty_ ~(handle_id:ID.t lazy_t) t : encoded_ty =
  let rec aux t = match T.repr t with
    | TI.TyArrow (a,b) ->
        let to_ = Lazy.force handle_id in
        U.ty_app (U.ty_const to_) [aux a; aux b]
    | _ -> U.map () t ~bind:(fun () v ->(),v) ~f:(fun () -> aux)
  in
  aux t

(* convert a handle to a proper encoded type *)
let ty_of_handle_ ~(handle_id:ID.t lazy_t) t : encoded_ty =
  let rec aux = function
    | H_leaf t -> t
    | H_arrow (t, h') ->
        let id = Lazy.force handle_id in
        U.ty_app (U.const id) [t; aux h']
  in
  aux t

(* build the handle [l_1 -> ... -> l_n -> h] where the [l_i] are encoded types *)
let rec handle_arrow_l l h = match l with
  | [] -> h
  | a :: l' -> H_arrow (a, handle_arrow_l l' h)

(* given an application function, generate the corresponding extensionality
   axiom: `forall f g. (f = g or exists x. f x != g x)` *)
let extensionality_for_app_ app_fun : (_,_) Stmt.t =
  let app_id = app_fun.af_id in
  let _, args, _ = U.ty_unfold app_fun.af_ty in
  match args with
  | [] -> assert false
  | handle :: args' ->
      (* handle: the actual function type;
         args': the actual arguments *)
      let f = Var.make ~ty:handle ~name:"f" in
      let g = Var.make ~ty:handle ~name:"g" in
      let vars =
        List.mapi
          (fun i ty -> Var.make ~ty ~name:("x_" ^ string_of_int i)) args'
      in
      let app_to_vars_ f l = U.app f (List.map U.var l) in
      let t1 = app_to_vars_ (U.const app_id) (f :: vars) in
      let t2 = app_to_vars_ (U.const app_id) (g :: vars) in
      let form =
        U.forall_l [f;g]
          (U.or_
            [ U.eq (U.var f) (U.var g)
            ; U.exists_l vars (U.neq t1 t2)
            ])
      in
      Stmt.axiom1 ~info:Stmt.info_default form

(* handle -> application symbol for this handle *)
let app_of_handle_ ~(state:state) (args:ty list) (ret:handle) : apply_fun =
  let handle_id = get_or_create_handle_id ~state in
  let h = U.ty_arrow_l args (ty_of_handle_ ~handle_id ret) in
  try Ty.Map.find h state.decode.app_symbols
  with Not_found ->
    let i = state.app_count in
    state.app_count <- i+1;
    let app_id = ID.make ("app_" ^ string_of_int i) in
    let ty_app = U.ty_arrow_l args (ty_of_handle_ ~handle_id ret) in
    Utils.debugf ~section 5 "@[<2>declare app_sym `@[%a :@ @[%a@]@]@ for handle @[%a@]@]`"
      (fun k->k ID.print app_id P.print ty_app P.print h);
    (* save application symbol in [app_symbols] *)
    let app_fun = {
      af_id=app_id;
      af_ty=ty_app;
      af_arity=List.length args;
    } in
    state.decode.app_symbols <- Ty.Map.add h app_fun state.decode.app_symbols;
    ID.Tbl.replace state.decode.dst_app_symbols app_id ();
    (* push declaration of [app_fun] and extensionality axiom *)
    let attrs = [Stmt.Attr_app_val] in
    let stmt = Stmt.decl ~info:Stmt.info_default ~attrs app_id ty_app in
    CCVector.push state.new_stmts stmt;
    CCVector.push state.new_stmts (extensionality_for_app_ app_fun);
    app_fun

(* split [l] into chunks of length given by elements of [lens] minus the
   previous length. Each chunk is paired with
   the remaining set of arguments. *)
let rec split_chunks_ prev lens l = match lens, l with
  | [], [] -> []
  | [], _ -> [l,[]]  (* return remaining elements *)
  | len :: lens', _ ->
      let c, l' = CCList.take_drop (len-prev) l in
      (c,l') :: split_chunks_ len lens' l'

let pp_chunks out =
  let pp_tys out = fpf out "@[%a@]" CCFormat.(list P.print) in
  let pp_pair out (a,b) = fpf out "@[(%a, remaining %a)@]" pp_tys a pp_tys b in
  fpf out "[@[%a@]]" CCFormat.(list ~start:"" ~stop:"" pp_pair)

(* introduce/get required app symbols for the given ID
   and store data structure that maps [arity -> sequence of apply symbs to use].
   @return the fun encoding for ID *)
let introduce_apply_syms ~state f : fun_encoding =
  let handle_id = get_or_create_handle_id ~state in
  let {as_set=set; as_ty_args=ty_args; as_ty_ret=ty_ret; _} =
    FunMap.find f state.arities
  in
  let l = IntSet.to_list set in
  let n = List.length ty_args in
  (* split type arguments into "blocks" *)
  assert (List.length l <= n + 1); (* +1: arity 0 exists *)

  (* encode type arguments and return type *)
  let ty_args = List.map (encode_ty_ ~handle_id) ty_args in
  let ty_ret = encode_ty_ ~handle_id ty_ret in

  let chunks = split_chunks_ 0 l ty_args in
  Utils.debugf ~section 4 "@[<2>process `%a :@ @[%a@]`@ chunks: @[%a@]@]"
    (fun k->k
      pp_fun f P.print (U.ty_arrow_l ty_args ty_ret) pp_chunks chunks);

  (* special case for first chunk, which doesn't need an application
     symbol *)
  let first_args, first_handle, n_args, app_l, m, chunks' =
    match chunks with
    | [] -> assert false
    | (args, remaining_args) :: chunks' ->
        (* first application: no app symbol, only the function itself *)
        let handle =
          handle_arrow_l remaining_args (H_leaf ty_ret)
          |> ty_of_handle_ ~handle_id |> handle_leaf in
        (* initial stack of applications *)
        let arity = List.length args in
        let app_l = [TC_first_param arity] in
        let m = IntMap.singleton arity app_l in
        args, handle, List.length args, app_l, m, chunks'
  in
  (* deal with remaining chunks. For each chunk we need the handle
     returned by the previous chunks (that is, if we apply arguments
     that come earlier, which handle type do we get?) *)
  let _, _, _, m =
    List.fold_left
      (fun (prev_handle, n_args, app_l, m) chunk ->
        (* we already applied the function to [n_args] using [app_l] *)
        let args, remaining_args = chunk in
        (* not the initial application: need an app symbol.
           type of app symbol is
            [handle := prev_handle -> args -> (remaining_args to ty_ret)] *)
        let handle_ret = handle_arrow_l remaining_args (H_leaf ty_ret) in
        let args' = ty_of_handle_ ~handle_id prev_handle :: args in
        let app_fun = app_of_handle_ ~state args' handle_ret in
        let n_args' = List.length args + n_args in
        let app_l' = TC_app app_fun :: app_l in
        let m = IntMap.add n_args' (List.rev app_l') m in
        (* return handle_ret, because it is the type obtained by
           fully applying [app_fun] *)
        handle_ret, n_args', app_l', m
      )
      (first_handle, n_args, app_l, m)
      chunks'
  in
  Utils.debugf ~section 4 "@[<hv2>map %a to@ %a@]"
    (fun k->k pp_fun f pp_fun_encoding m);

  let fe = {
    fe_stack=m;
    fe_args=first_args;
    fe_ret_handle=first_handle;
  } in

  state.decode.fun_encodings <- FunMap.add f fe state.decode.fun_encodings;

  fe

(* obtain or compute the fun encoding for [id] *)
let fun_encoding_for ~state (f:fun_) : fun_encoding =
  try FunMap.find f state.decode.fun_encodings
  with Not_found -> introduce_apply_syms ~state f

let sc_arity_ = function
  | TC_first_param n -> n
  | TC_app a -> a.af_arity

(* apply the list of apply_fun to [l]. Arities should match. *)
let rec apply_app_funs_ tower l =
  Utils.debugf ~section 5 "@[<2>apply_tower@ @[%a@]@ to @[%a@]@]"
    (fun k->k pp_fe_tower tower (CCFormat.list P.print) l);
  match tower with
  | [] ->
      begin match l with
      | []
      | _::_::_ -> assert false
      | [res] -> res
      end
  | f :: tower' ->
      let arity = sc_arity_ f in
      let head, (args, l') = match f, l with
        | _, [] -> assert false
        | TC_first_param _, f :: args' ->
            (* first parameter on the tower = the function to apply *)
            f, CCList.take_drop arity args'
        | TC_app af, _ ->
            U.const af.af_id, CCList.take_drop arity l
      in
      assert (List.length args = arity);
      (* compute closure, then push it on l *)
      let closure = U.app head args in
      apply_app_funs_ tower' (closure :: l')

let elim_hof_ty ~state subst ty =
  let handle_id = get_or_create_handle_id ~state in
  encode_ty_ ~handle_id (U.eval_renaming ~subst ty)

(* new type of the function that has this encoding *)
let ty_of_fun_encoding_ ~state fe =
  let handle_id = get_or_create_handle_id ~state in
  U.ty_arrow_l fe.fe_args (ty_of_handle_ ~handle_id fe.fe_ret_handle)

let ty_term_ ~state t =
  U.ty_exn ~sigma:(Env.find_ty ~env:state.env) t

type renaming_subst = (T.t, T.t Var.t) Subst.t

(* encode [v]'s type, and add it to [subst] *)
let bind_hof_var ~state (subst:renaming_subst) v =
  (* replace [v] with [v'], which has an encoded type *)
  let v' = Var.update_ty v ~f:(elim_hof_ty ~state subst) in
  let subst = Subst.add ~subst v v' in
  subst, v'

let bind_hof_vars ~state subst l =
  Utils.fold_map (bind_hof_var ~state) subst l

(* traverse [t] and replace partial applications with fully applied symbols
    from state.app_symbols. Also encodes every type using [handle_id] *)
let elim_hof_term ~state subst pol t =
  let rec aux subst pol t = match T.repr t with
    | TI.Var v -> Subst.find_exn ~subst v |> U.var
    | TI.TyArrow _ -> aux_ty subst t (* type: encode it *)
    | TI.App (f,l) ->
        let as_hof = match T.repr f with
          | TI.Const id when FunMap.mem (F_id id) state.arities ->
            let fe = fun_encoding_for ~state (F_id id) in
            Some (f, fe)
          | TI.Var v when FunMap.mem (F_var v) state.arities ->
            let f' = U.var (Subst.find_exn ~subst v) in
            let fe = fun_encoding_for ~state (F_var v) in
            Some (f', fe)
          | TI.Builtin (`DataSelect (id_c, i))
            when FunMap.mem (F_select (id_c,i)) state.arities ->
            let fe = fun_encoding_for ~state (F_select (id_c,i)) in
            Some (f, fe)
          | _ -> None
        in
        begin match as_hof with
          | Some (new_f, fun_encoding) ->
            let l = List.map (aux subst Pol.NoPol) l in
            (* replace by applications symbols, based on [length l] *)
            let n = List.length l in
            (* stack of application functions to use *)
            let app_l = IntMap.find n fun_encoding.fe_stack in
            apply_app_funs_ app_l (new_f::l)
          | None ->
            aux' subst pol t
        end
    | TI.Bind ((`Forall | `Exists) as q, v, _) when var_is_ho_ v ->
      begin match U.approx_infinite_quant_pol q pol with
        | `Keep -> aux' subst pol t  (* ok *)
        | `Unsat_means_unknown res ->
          state.unsat_means_unknown <- true;
          Utils.debugf ~section 3
            "@[<2>encode `@[%a@]`@ as `@[%a@]`,@ quantifying over type `@[%a@]`@]"
            (fun k->k P.print t P.print res P.print (Var.ty v));
          res
      end
    | TI.Builtin (`Eq (a,_)) when ty_is_ho_ (ty_term_ ~state a) ->
      (* higher-order comparison --> requires approximation *)
      (* TODO:
         [a = b asserting has_proto a] for noPol,
         [a = b && has_proto a] for Pos*)
      begin match U.approx_infinite_quant_pol `Eq pol with
        | `Keep -> aux' subst pol t (* fine *)
        | `Unsat_means_unknown res ->
          state.unsat_means_unknown <- true;
          Utils.debugf ~section 3
            "@[<2>encode HO equality `@[%a@]`@ as `@[%a@]`@]"
            (fun k->k P.print t P.print res);
          res
      end
    | TI.Let _
    | TI.Bind _
    | TI.Match _
    | TI.Const _
    | TI.Builtin _
    | TI.TyBuiltin _
    | TI.TyMeta _ -> aux' subst pol t
  (* traverse subterms of [t] *)
  and aux' subst pol t =
    U.map_pol subst pol t
      ~f:aux
      ~bind:(bind_hof_var ~state)
  and aux_ty subst ty =
    let handle_id = get_or_create_handle_id ~state in
    encode_ty_ ~handle_id (U.eval_renaming ~subst ty)
  in
  aux subst pol t

(* given a (function) type, encode its arguments and return type but
   keeps the toplevel arrows *)
let encode_toplevel_ty ~state ty =
  let handle_id = get_or_create_handle_id ~state in
  let tyvars, args, ret = U.ty_unfold ty in
  assert (tyvars=[]);
  let args = List.map (encode_ty_ ~handle_id) args in
  let ret = encode_ty_ ~handle_id ret in
  U.ty_arrow_l args ret

(* translate a "single rec" into an "app rec" *)
let elim_hof_rec ~info ~state (defs:(_,_) Stmt.rec_defs)
: (_, _) Stmt.t list
=
  let elim_eqn
    : (term,ty) Stmt.rec_def -> (term,ty) Stmt.rec_def
    = fun def ->
      let defined = def.Stmt.rec_defined in
      let id = defined.Stmt.defined_head in
      match def.Stmt.rec_eqns with
      | Stmt.Eqn_single (vars, rhs) ->
          if FunMap.mem (F_id id) state.arities then (
            (* higher-order function *)
            let fe = introduce_apply_syms ~state (F_id id) in
            let arity = List.length vars in
            Utils.debugf ~section 5
              "@[<2>transform def of %a (arity %d) into App_rec@]"
              (fun k->k ID.print id arity);
            (* stack of apply function *)
            let stack =
              try IntMap.find arity fe.fe_stack
              with Not_found ->
                errorf_ "rec-defined function %a should have full arity %d"
                  ID.print id arity
            in
            let subst, vars = bind_hof_vars ~state Subst.empty vars in
            (* LHS: app (f x y) z *)
            let lhs =
              apply_app_funs_ stack
                (U.const id :: List.map U.var vars)
            in
            let rhs = elim_hof_term ~state subst (ID.polarity id) rhs in
            let app_l =
              List.map
                (function TC_first_param _ -> id | TC_app a -> a.af_id) stack in
            let eqn = Stmt.Eqn_app (app_l, vars, lhs, rhs) in
            let defined =
              Stmt.mk_defined id ~attrs:defined.Stmt.defined_attrs
                (ty_of_fun_encoding_ ~state fe)
            in
            { Stmt.
              rec_defined=defined;
              rec_ty_vars=[];
              rec_eqns=eqn;
            }
          ) else (
            Utils.debugf ~section 5
              "@[<2>keep structure of FO def of `%a`@]" (fun k->k ID.print id);
            let tr_term = elim_hof_term ~state in
            let tr_type _subst ty = encode_toplevel_ty ~state ty in
            Stmt.map_rec_def_bind Subst.empty def
              ~bind:(bind_hof_var ~state) ~term:tr_term ~ty:tr_type
          )
      | Stmt.Eqn_nested _
      | Stmt.Eqn_app _ -> assert false
  in
  let defs = List.map elim_eqn defs in
  [Stmt.axiom_rec ~info defs]

(* eliminate partial applications in the given statement. Can return several
   statements because of the declarations of new application symbols. *)
let elim_hof_statement ~state stmt : (_, _) Stmt.t list =
  let info = Stmt.info stmt in
  let tr_term = elim_hof_term ~state in
  let tr_type _subst ty = encode_toplevel_ty ~state ty in
  let handle_id = get_or_create_handle_id ~state in
  Utils.debugf ~section 3 "@[<2>@{<cyan>> elim HOF in stmt@}@ `@[%a@]`@]" (fun k->k PStmt.print stmt);
  (* find the new type of the given partially applied function [id : ty] *)
  let encode_fun id =
    Utils.debugf ~section 3
      "introduce application symbols and handle types for %a…"
      (fun k->k ID.print id);
    let fun_encoding = introduce_apply_syms ~state (F_id id) in
    let ty' =
      U.ty_arrow_l fun_encoding.fe_args
        (ty_of_handle_ ~handle_id fun_encoding.fe_ret_handle) in
    Utils.debugf ~section 4 "@[<2>fun %a now has type `@[%a@]`@]"
      (fun k->k ID.print id P.print ty');
    ty'
  in
  let stmt' = match Stmt.view stmt with
  | Stmt.Decl d ->
      let id = Stmt.id_of_defined d in
      let ty' =
        if FunMap.mem (F_id id) state.arities
        then encode_fun id
        else encode_toplevel_ty ~state (Stmt.ty_of_defined d)
            (* keep as is, not a partially applied fun; still have to modify type *)
      in
      [Stmt.decl ~info id ty' ~attrs:(Stmt.attrs_of_defined d)]
  | Stmt.Axiom (Stmt.Axiom_rec l) -> elim_hof_rec ~state ~info l
  | Stmt.Axiom (Stmt.Axiom_spec spec) ->
      let subst, vars =
        Utils.fold_map (bind_hof_var ~state) Subst.empty spec.Stmt.spec_ty_vars
      in
      let spec =
        { Stmt.
          spec_axioms=List.map (tr_term subst Pol.Pos) spec.Stmt.spec_axioms;
          spec_ty_vars=vars;
          spec_defined=
            List.map
              (fun d ->
                 let id = Stmt.id_of_defined d in
                 let ty = Stmt.ty_of_defined d in
                 let attrs = Stmt.attrs_of_defined d in
                 let ty' =
                   if FunMap.mem (F_id id) state.arities
                   then encode_fun id
                   else encode_toplevel_ty ~state ty
                 in
                 Stmt.mk_defined ~attrs id ty')
              spec.Stmt.spec_defined;
        } in
      [Stmt.axiom_spec ~info spec]
  | Stmt.TyDef (kind,l) ->
      let l =
        let open Stmt in
        List.map
          (fun tydef ->
             { tydef with
               ty_cstors =
                 ID.Map.map
                   (fun c ->
                      { c with
                        cstor_args=List.map (encode_ty_ ~handle_id) c.cstor_args;
                        cstor_type=encode_toplevel_ty ~state c.cstor_type;
                      })
                   tydef.ty_cstors;
               ty_type = encode_toplevel_ty ~state tydef.ty_type;
             })
          l
      in
      [Stmt.mk_ty_def ~info kind l]
  | Stmt.Copy c ->
      let subst, copy_vars = bind_hof_vars ~state Subst.empty c.Stmt.copy_vars in
      let copy_of = encode_ty_ ~handle_id c.Stmt.copy_of in
      let copy_to = encode_ty_ ~handle_id c.Stmt.copy_to in
      let copy_wrt = match c.Stmt.copy_wrt with
        | Stmt.Wrt_nothing -> Stmt.Wrt_nothing
        | Stmt.Wrt_subset p -> Stmt.Wrt_subset (tr_term subst Pol.NoPol p)
        | Stmt.Wrt_quotient (tty, r) -> Stmt.Wrt_quotient (tty, tr_term subst Pol.NoPol r)
      in
      let c' = {
        c with Stmt.
          copy_wrt;
          copy_vars;
          copy_of;
          copy_to;
          copy_abstract_ty=U.ty_arrow copy_of copy_to;
          copy_concrete_ty=U.ty_arrow copy_to copy_of;
      } in
      [Stmt.copy ~info c']
  | Stmt.Axiom _
  | Stmt.Pred (_,_,_)
  | Stmt.Goal _ ->
      let stmt' =
        Stmt.map_bind Subst.empty stmt
          ~bind:(bind_hof_var ~state) ~term:tr_term ~ty:tr_type
      in
      [stmt']
  in
  (* obtain new type declarations, new axioms, etc. *)
  let new_stmts = state.new_stmts |> CCVector.to_list in
  CCVector.clear state.new_stmts;
  if new_stmts<>[]
  then Utils.debugf ~section 3 "@[<2>@{<cyan>< new declarations@}:@ @[<v>%a@]@]"
    (fun k->k (CCFormat.list ~start:"" ~stop:"" ~sep:"" PStmt.print) new_stmts);
  Utils.debugf ~section 3 "@[<2>@{<cyan>< obtain stmts@}@ `[@[<hv>%a@]]`@]"
    (fun k->k (CCFormat.list ~start:"" ~stop:"" PStmt.print) stmt');
  new_stmts @ stmt'

let elim_hof pb =
  let env = Problem.env pb in
  (* compute arities *)
  let arities = compute_arities_pb ~env:env pb in
  Utils.debugf ~section 3 "@[<2>arities of partially applied functions:@ @[<v>%a@]@]"
    (fun k->k pp_arities arities);
  (* introduce application symbols and sorts *)
  let state = create_state ~env arities in
  let pb' =
    Problem.flat_map_statements pb
      ~f:(elim_hof_statement ~state)
  in
  let pb' = Problem.add_unsat_means_unknown state.unsat_means_unknown pb' in
  (* return new problem *)
  pb', state.decode

(** {2 Decoding} *)

module M = Model
module DT = M.DT

type const_map = ID.t -> T.t

(* traverse [t], decoding the types in every variable and replacing
   [to a b] by [a -> b]
    @param subst substitution for renaming variables, etc.
    @param map map some constants to other terms *)
let rec decode_term ~state ~(map:const_map) subst t =
  Utils.debugf ~section 5 "@[<2>decode_term `@[%a@]`@ with @[%a@]@]"
    (fun k->k P.print t (Subst.print P.print) subst);
  match T.repr t with
  | TI.Const id -> map id (* translate this [id], if needed *)
  | TI.Var v -> Subst.find_or ~subst ~default:t v
  | TI.App (f, l) ->
      begin match T.repr f, state.dst_handle_id, l with
        | TI.Const id, Some id', [a;b] when ID.equal id id' ->
            (* [to a b] becomes [a -> b] again *)
            U.ty_arrow
              (decode_term ~state ~map subst a)
              (decode_term ~state ~map subst b)
        | TI.Const id, _, hd :: l' when ID.Tbl.mem state.dst_app_symbols id ->
            (* app symbol: remove app, apply [hd] to [l'] and evaluate *)
            let hd = decode_term ~state ~map subst hd in
            let l' = List.map (decode_term ~state ~map subst) l' in
            Red.app_whnf hd l'
        | _ -> decode_term' ~state ~map subst t
      end
  | _ -> decode_term' ~state ~map subst t

and decode_term' ~state ~map subst t =
  U.map subst t
    ~bind:(bind_decode_var_ ~state ~map)
    ~f:(decode_term ~state ~map)

and bind_decode_var_ ~state ~map subst v =
  let v' = Var.fresh_copy v in
  let v' = Var.update_ty v' ~f:(decode_term ~state ~map subst) in
  Subst.add ~subst v (U.var v'), v'

(* find discrimination tree for [id], from functions or constants of [m]  *)
let find_dt_ m id =
  (* search in both functions and constants *)
  let res =
    CCList.find_map
      (fun (f,dt,k) -> match T.repr f with
         | TI.Const id' when ID.equal id id' -> Some (dt,k)
         | _ -> None)
      m.Model.values
  in
  match res with
    | None -> errorf_ "could not find model for function %a" ID.print id
    | Some tup -> tup

(* translate a DT's terms and variables *)
let tr_dt ?(subst=Subst.empty) ~state ~map dt =
  Utils.debugf ~section 5 "@[<hv2>decode@ `@[%a@]`@ with @[%a@]@]"
    (fun k->k
        (Model.DT.print P.print' P.print) dt (Subst.print P.print) subst);
  (* first, replace vars *)
  let dt' =
    let vars = DT.vars dt in
    let vars' =
      List.map (Var.fresh_update_ty ~f:(decode_term ~state ~map subst)) vars
    in
    let subst_v = Subst.of_list vars vars' in
    M.DT_util.map_vars ~subst:subst_v dt
  in
  let tr_ t  = decode_term ~state ~map subst t in
  Model.DT.map dt' ~term:tr_ ~ty:tr_

(* see if type is a handle *)
let as_handle_ ~state ty : handle option =
  let is_handle_ i = match state.dst_handle_id with
    | None -> false
    | Some i' -> ID.equal i i'
  in
  let is_handle_cst t = match T.repr t with TI.Const i -> is_handle_ i | _ -> false in
  let rec aux ty = match T.repr ty with
    | TI.App (f, [a;b]) when is_handle_cst f ->
      let b1, b2 = aux b in a :: b1, b2
    | _ -> [], ty
  in
  match aux ty with
    | [], _ -> None
    | args,ret -> Some (handle_arrow_l args (H_leaf ret))

let is_handle_ ~state ty : bool = CCOpt.is_some (as_handle_ ~state ty)

(* all domain constants whose type is a handle *)
let all_fun_consts_ ~state m : (ty * handle) ID.Map.t =
  Model.fold ID.Map.empty m
    ~finite_types:(fun m (ty,ids) ->
      match as_handle_ ~state ty with
        | None -> m
        | Some h ->
          Utils.debugf ~section 5
            "@[<2>type `@[%a@]`@ is a handle type @[%a@],@ for %a@]"
            (fun k->k P.print ty pp_handle h (CCFormat.list ID.print) ids);
          List.fold_left (fun m i -> ID.Map.add i (ty,h) m) m ids
    )

let new_fun_name_ ~state =
  let id = ID.make_f "$$anon_fun_%d" state.dst_gensym in
  state.dst_gensym <- state.dst_gensym + 1;
  id

(* compute a map from constants of type "to a (to b c)" to fresh names
   of type "a -> b -> c", defined on the side.
   @return the map, and a list of definitions *)
let map_ho_consts_to_funs ~state m : const_map * (unit -> (_,_) M.value_def list) =
  let const_tbl : T.t ID.Tbl.t = ID.Tbl.create 16 in
  let fun_defs : (_,_) M.value_def list ref = ref [] in
  let all_fun_const = all_fun_consts_ ~state m in
  let add_to_tbl id t =
    ID.Tbl.add const_tbl id t;
    Utils.debugf ~section 5
      "@[<2>translate name %a into %a@]" (fun k->k ID.print id P.print t);
  in
  (* if [id] is a domain constant, then map it to a lambda term,
     otherwise keep it intact *)
  let rec map_id
    : const_map
    = fun id -> match ID.Map.get id all_fun_const with
    | None -> U.const id
    | Some (ty,h) ->
      begin match ID.Tbl.get const_tbl id with
        | Some t -> t
        | None -> tr_functional_cst id ty h
      end
  (* find the function corresponding to
     the constant [c] of type [to 'a (to 'b 'c)];
     @param app the application symbol corresponding to [to 'a (to 'b 'c)]
     @param ty the decoded (arrow) type ['a -> 'b -> 'c] *)
  and tr_functional_cst (id:ID.t) (ty:ty) (h:handle) =
    (* find corresponding "apply" symbol *)
    let handle_id = get_handle_id_decode ~state in
    let ty' = decode_term ~state ~map:map_id Subst.empty ty in
    let ty_app = U.ty_arrow (ty_of_handle_ ~handle_id h) ty' in
    begin match Ty.Map.get ty_app state.app_symbols with
      | Some app ->
        tr_partial_fun app.af_id ty' id
      | None ->
        Utils.debugf ~section 5
          "cannot find app symbol for `@[%a@],@ handle `@[%a@]`,@ full type `@[%a@]``"
          (fun k->k ID.print id pp_handle h P.print ty_app);
        (* return a new undefined function *)
        let _, ty_args, ty_ret = U.ty_unfold ty' in
        let vars =
          List.mapi (fun i ty -> Var.makef ~ty "_%d" i) ty_args
        and body =
          let id' =
            ID.make_f "_%s_%d" (Ty.mangle ~sep:"_" ty_ret) (ID.Tbl.length const_tbl)
          in
          U.undefined_self (U.const id')
        in
        let t = U.fun_l vars body in
        add_to_tbl id t;
        t
    end
  (* translate back this partially applied function
     @param app the application symbol *)
  and tr_partial_fun (app:ID.t) ty (c:ID.t) =
    Utils.debugf ~section 5
      "@[<2>tr fun constant `@[%a@] : @[%a@]`@ with app symbol `%a`@]"
      (fun k->k ID.print c P.print ty ID.print app);
    let _, _args, ret = U.ty_unfold ty in
    (* give a name to the function *)
    let c' = new_fun_name_ ~state in
    let t' = U.const c' in
    add_to_tbl c t';
    (* compute the body of the lambda *)
    let dt = compute_dt app c in
    let k = if U.ty_is_Prop ret then M.Symbol_prop else M.Symbol_fun in
    CCList.Ref.push fun_defs (t', dt, k);
    Utils.debugf ~section 5
      "@[... decode `%a`@ into `@[%a@ := @[%a@]@]`@]"
      (fun k->k ID.print c ID.print c' M.DT_util.print dt);
    t'
  (* compute a decision tree for this constant *)
  and compute_dt app (c:ID.t) : (_,_) DT.t =
    let dt, _ = find_dt_ m app in
    M.DT_util.apply dt (U.const c)
    |> tr_dt ~subst:Subst.empty ~state ~map:map_id
  in
  map_id, (fun () -> !fun_defs)

(* Assuming [f_id = f_const] is a part of the model [m], and [f_id] is
   a function encoded using [tower], find the actual value of [f_id] in
   the model [m] by flattening/filtering discrimination trees for functions
   of [tower].
   @return new discrimination tree, function kind *)
let extract_subtree_ m f_id tower : (_,_) DT.t * M.symbol_kind =
  Utils.debugf ~section 5 "@[<2>extract subtree for @[%a@]@]" (fun k->k pp_fe_tower tower);
  (* @param hd: first parameter, that is, the partial function being applied *)
  let rec aux hd tower = match tower with
    | [] -> assert false
    | TC_first_param _ :: _ -> assert false
    | [TC_app af] -> find_dt_ m af.af_id
    | TC_app af :: tower' ->
        (* find and transform [dt] for [f] *)
        let dt, _ = find_dt_ m af.af_id in
        (* first variable, is replaced by [hd] *)
        let vars = match DT.vars dt with
          | _::b -> b
          | [] -> assert false
        in
        let hd = U.app hd (List.map U.var vars) in
        (* merge with [dt] for remaining tower functions *)
        let dt', k = aux hd tower' in
        let new_dt = M.DT_util.join dt dt' in
        new_dt, k
  in
  match tower with
    | []
    | TC_app _ ::_ -> assert false
    | TC_first_param _ :: tower' ->
        let dt, _ = find_dt_ m f_id in
        (* in the surrounding application symbols, replace first arg with [hd] *)
        let vars = DT.vars dt in
        let hd = U.app_const f_id (List.map U.var vars) in
        (* merge with rest of DT *)
        let dt', k = aux hd tower' in
        let new_dt = M.DT_util.join dt dt' in
        new_dt, k

(* for every function [f], look its fun_encoding for full arity so as
   to obtain the tower. Lookup models for every app symbol involved and
   collapse the corresponding branches of decision tree.
   if [f] occurs with arity 0 it will still need a name/constant so the
   model of its callers can refer to it. *)
let decode_model ~state m =
  Utils.debug ~section 1 "decode model…";
  (* first, compute a map from constants of functional type,
     to actual lambda expressions *)
  let map, new_funs = map_ho_consts_to_funs ~state m in
  let tr_term = decode_term ~state ~map Subst.empty in
  (* partially applied fun: obtain the corresponding tree from
     application symbols (pick  the tower of application symbols corresponding
     to [id]'s full arity. *)
  let decode_partial_fun_ new_m id =
    let tower =
      FunMap.find (F_id id) state.fun_encodings
      |> (fun fe -> fe.fe_stack)
      |> IntMap.max_binding
      |> snd
    in
    let dt, k = extract_subtree_ m id tower in
    let dt = tr_dt ~state ~map dt in
    Model.add_value new_m (U.const id, dt, k)
  in
  Model.fold (Model.empty_copy m) m
    ~finite_types:(fun new_m (ty,cases) ->
      match T.repr ty, state.dst_handle_id with
        | TI.Const id, Some id' when ID.equal id id' -> new_m (* drop handle type *)
        | _ when is_handle_ ~state ty -> new_m (* drop handle types *)
        | _ -> Model.add_finite_type new_m (tr_term ty) cases)
    ~values:(fun new_m (t,dt,k) -> match T.repr t with
      | TI.Const id when FunMap.mem (F_id id) state.fun_encodings ->
        decode_partial_fun_ new_m id
      | TI.Const id when ID.Tbl.mem state.dst_app_symbols id ->
        new_m (* drop application symbols from model *)
      | _ ->
        let t = tr_term t in
        let dt = tr_dt ~state ~map dt in
        Model.add_value new_m (t, dt, k)
    )
  |> (fun m -> List.fold_left Model.add_value m (new_funs ()))

(** {2 Pipe} *)

let pipe_with ?on_decoded ~decode ~print ~check =
  let on_encoded =
    Utils.singleton_if print () ~f:(fun () ->
      let module PPb = Problem.Print(P)(P) in
      Format.printf "@[<v2>@{<Yellow>after elimination of HOF@}: %a@]@." PPb.print)
    @
    Utils.singleton_if check () ~f:(fun () ->
      let module C = TypeCheck.Make(T) in
      C.empty () |> C.check_problem)
  in
  Transform.make
    ?on_decoded
    ~on_encoded
    ~input_spec:Transform.Features.(of_list
          [Ty, Mono; Ind_preds, Absent; Eqn, Eqn_single])
    ~map_spec:Transform.Features.(update_l [Eqn, Eqn_app; HOF, Absent])
    ~name
    ~encode:(fun p ->
      let p, state = elim_hof p in
      p, state
    )
    ~decode
    ()

let pipe ~print ~check =
  let on_decoded = if print
    then
      [Format.printf "@[<2>@{<Yellow>res after elim_HOF@}:@ %a@]@."
         (Problem.Res.print P.print' P.print)]
    else []
  in
  let decode state = Problem.Res.map_m ~f:(decode_model ~state) in
  pipe_with ~on_decoded ~print ~decode ~check
