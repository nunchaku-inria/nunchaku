
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
module Red = Reduce.Make(T)

let name = "elim_hof"
let section = Utils.Section.make name

type inv1 = <ty:[`Mono]; eqn:[`Single]; ind_preds: [`Absent]>
type inv2 = <ty:[`Mono]; eqn:[`App]; ind_preds: [`Absent]>

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

    The point here is to find, for every function symbol, the set of
    arities it is (partially) applied with.
    Only functions partially applied at least once are of interest
    in this section. *)

module IntSet = CCSet.Make(CCInt)
module IntMap = CCMap.Make(CCInt)

type arity_set = {
  as_set : IntSet.t;
  as_ty_args : term list; (* shortcut to the type arguments of the function *)
  as_ty_ret : term; (* shortcut to the return type of the function *)
}

let pp_arity_set out set =
  fpf out "{@[%a@]}" (IntSet.print ~start:"" ~stop:"" CCFormat.int) set.as_set

(* print arity map *)
let pp_arities out tbl =
  let pp_pair out (id,set) = fpf out "@[%a → @[%a@] over %d@]"
    ID.print_full id pp_arity_set set (List.length set.as_ty_args)
  in
  fpf out "@[<v>%a@]"
    (CCFormat.seq ~start:"" ~stop:"" ~sep:"" pp_pair)
    (ID.Map.to_seq tbl)

(* With [id : ty_args -> ty_ret], report a use of [id] with [n] arguments
   where [n <= List.length ty_args] *)
let add_arity_ m id n ty_args ty_ret =
  let set =
    try ID.Map.find id m
    with Not_found ->
      { as_set=IntSet.empty;
        as_ty_args=ty_args;
        as_ty_ret=ty_ret;
      }
  in
  let set = {set with as_set=IntSet.add n set.as_set;} in
  ID.Map.add id set m

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
  add_arity_ m (Var.id v) 0 args ret

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
            m := add_arity_ !m id 0 ty_args ty_ret
        end
    | TMI.Var v when var_is_ho_ v ->
        (* higher order variable *)
        m := add_arity_var_ !m v
    | TMI.App (f, l) ->
        assert (l<>[]);
        begin match TM.repr f with
        | TMI.Const id ->
            begin match as_fun_ ~env id with
              | Some ([],_) -> assert false
              | None -> ()   (* not a function *)
              | Some (ty_args, ty_ret) ->
                  assert (List.length ty_args >= List.length l);
                  m := add_arity_ !m id (List.length l) ty_args ty_ret
            end;
            (* explore subterms *)
            List.iter aux l
        | TMI.Var v ->
            assert (var_is_ho_ v);
            (* higher order variable applied to [l] *)
            let tyvars, args, ret = U.ty_unfold (Var.ty v) in
            assert (tyvars=[]); (* mono, see {!inv} *)
            assert (List.length args >= List.length l);
            m := add_arity_ !m (Var.id v) (List.length l) args ret
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
          m := add_arity_ !m (Var.id v) 0 args ret
        ))
  in
  aux t;
  !m

(* NOTE: we consider that all functions are always totally applied at least
   once, so that the app symbol and extensionality axioms are generated.

   TODO: optim: do not do that if remaining args are guaranteed to be of
   infinite cardinality (extensionality not strictly needed then). Problem
   is for [unit -> unit] and the likes. *)

let compute_arities_stmt ~env m (stmt:(_,_,inv1) Stmt.t) =
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
            let m = add_full_arity id def.Stmt.rec_defined.Stmt.defined_ty m in
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
        |> add_full_arity c.Stmt.copy_abstract c.Stmt.copy_abstract_ty
        |> add_arity1 c.Stmt.copy_abstract c.Stmt.copy_abstract_ty
        |> add_full_arity c.Stmt.copy_concrete c.Stmt.copy_concrete_ty
        |> add_arity1 c.Stmt.copy_concrete c.Stmt.copy_concrete_ty
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
    |> CCVector.fold (compute_arities_stmt ~env) ID.Map.empty
  in
  (* remove functions that are always fully applied *)
  ID.Map.filter
    (fun _id set -> not (always_fully_applied_ set))
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

(* map from handles to 'a *)
module HandleMap = struct
  type +'a t = {
    leaves: (ty * 'a) list;  (* maps [H_leaf t] to a value, for various [t] *)
    arrows: (ty * 'a t) list; (* maps [H_arrow (t, h')] to a subtree for [h'] *)
  }

  let empty = {leaves=[]; arrows=[];}

  (* find binding for [h] in [m], or raise Not_found *)
  let rec find_exn h m = match h with
    | H_leaf t -> CCList.Assoc.get_exn ~eq:U.equal m.leaves t
    | H_arrow (t, h') ->
        let m' = CCList.Assoc.get_exn ~eq:U.equal m.arrows t in
        find_exn h' m'

  (* add [h -> v] to map [m] *)
  let rec add h v m = match h with
    | H_leaf t ->
        let leaves = CCList.Assoc.set ~eq:U.equal m.leaves t v in
        {m with leaves;}
    | H_arrow (t, h') ->
        let arrows =
          try
            let m' = CCList.Assoc.get_exn ~eq:U.equal m.arrows t in
            let m' = add h' v m' in
            CCList.Assoc.set ~eq:U.equal m.arrows t m'
          with Not_found ->
            (t, add h' v empty) :: m.arrows
        in
        {m with arrows; }
end

(** {2 State for Encoding and Decoding} *)

(* application symbol (for partial application) *)
type apply_fun = {
  af_id: ID.t;
  af_ty: term; (* type of the function *)
  af_arity: int; (* shortcut: number of arguments *)
}

type fun_encoding_tower_cell =
  | TC_app of apply_fun (* use this "app" function *)
  | TC_first_param of ID.t * int (* apply the first parameter (given its arity) *)

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
  mutable fun_encodings: fun_encoding ID.Map.t;
    (* partially applied function/variable -> how to encode it *)
  mutable app_symbols: apply_fun HandleMap.t;
    (* handle type -> corresponding apply symbol *)
  mutable dst_gensym: int;
    (* counter for new symbols *)
}

type state = {
  env: (term, ty, inv1) Env.t;
    (* environment (to get signatures, etc.) *)
  arities: arity_set ID.Map.t;
    (* set of arities for partially applied symbols/variables *)
  mutable app_count: int;
    (* used for generating new names *)
  mutable new_stmts : (term, ty, inv2) Stmt.t CCVector.vector;
    (* used for new declarations. [id, type, attribute list] *)
  mutable lost_completeness: bool;
    (* did we have to do some approximation? *)
  decode: decode_state;
    (* bookkeeping for, later, decoding *)
}

let pp_apply_fun out f =
  fpf out "@[<2>%a/%d :@ `@[%a@]`@]" ID.print f.af_id f.af_arity P.print f.af_ty

let pp_sc out = function
  | TC_first_param (f,n) -> fpf out "%a (arity %d)" ID.print f n
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
  lost_completeness=false;
  decode={
    dst_app_symbols=ID.Tbl.create 16;
    dst_gensym=0;
    dst_handle_id=None;
    fun_encodings=ID.Map.empty;
    app_symbols=HandleMap.empty;
  };
}

(** {2 Encoding} *)

let get_handle_id_ ~state = match state.decode.dst_handle_id with
  | Some i -> i
  | None ->
      let id = ID.make "to" in
      state.decode.dst_handle_id <- Some id;
      let ty_id = U.ty_arrow_l [U.ty_type; U.ty_type] U.ty_type in
      (* declare the symbol [to : type -> type -> type] *)
      let attrs =
        [ Stmt.Attr_exn ElimRecursion.Attr_is_handle_cstor
        ; Stmt.Attr_incomplete
        ] in
      let stmt = Stmt.decl ~info:Stmt.info_default ~attrs id ty_id in
      CCVector.push state.new_stmts stmt;
      id

(* encode a type parameter so it becomes first-order (replace [->] with [to]) *)
let encode_ty_ ~state t : encoded_ty =
  let rec aux t = match T.repr t with
    | TI.TyArrow (a,b) ->
        let to_ = get_handle_id_ ~state in
        U.ty_app (U.ty_const to_) [aux a; aux b]
    | _ -> U.map () t ~bind:(fun () v ->(),v) ~f:(fun () -> aux)
  in
  aux t

(* convert a handle to a proper encoded type *)
let ty_of_handle_ ~state t : encoded_ty =
  let rec aux = function
    | H_leaf t -> t
    | H_arrow (t, h') ->
        let id = get_handle_id_ ~state in
        U.ty_app (U.const id) [t; aux h']
  in
  aux t

(* build the handle [l_1 -> ... -> l_n -> h] where the [l_i] are encoded types *)
let rec handle_arrow_l l h = match l with
  | [] -> h
  | a :: l' -> H_arrow (a, handle_arrow_l l' h)

(* given an application function, generate the corresponding extensionality
   axiom: `forall f g. (f = g or exists x. f x != g x)` *)
let extensionality_for_app_ app_fun : (_,_,_) Stmt.t =
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
let app_of_handle_ ~state args ret : apply_fun =
  let h = handle_arrow_l args ret in
  try HandleMap.find_exn h state.decode.app_symbols
  with Not_found ->
    let i = state.app_count in
    state.app_count <- i+1;
    let app_id = ID.make ("app_" ^ string_of_int i) in
    let ty_app = U.ty_arrow_l args (ty_of_handle_ ~state ret) in
    Utils.debugf ~section 5 "@[<2>declare app_sym `@[%a :@ @[%a@]@]@ for handle @[%a@]@]`"
      (fun k->k ID.print app_id P.print ty_app pp_handle h);
    (* save application symbol in [app_symbols] *)
    let app_fun = {
      af_id=app_id;
      af_ty=ty_app;
      af_arity=List.length args;
    } in
    state.decode.app_symbols <- HandleMap.add h app_fun state.decode.app_symbols;
    ID.Tbl.replace state.decode.dst_app_symbols app_id ();
    (* push declaration of [app_fun] and extensionality axiom *)
    let attrs = [Stmt.Attr_exn ElimRecursion.Attr_app_val] in
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
let introduce_apply_syms ~state id =
  let {as_set=set; as_ty_args=ty_args; as_ty_ret=ty_ret; _} =
    ID.Map.find id state.arities
  in
  let l = IntSet.to_list set in
  let n = List.length ty_args in
  (* split type arguments into "blocks" *)
  assert (List.length l <= n + 1); (* +1: arity 0 exists *)

  (* encode type arguments and return type *)
  let ty_args = List.map (encode_ty_ ~state) ty_args in
  let ty_ret = encode_ty_ ~state ty_ret in

  let chunks = split_chunks_ 0 l ty_args in
  Utils.debugf ~section 4 "@[<2>process %a :@ `@[%a@]`@ chunks: @[%a@]@]"
    (fun k->k
      ID.print id P.print (U.ty_arrow_l ty_args ty_ret) pp_chunks chunks);

  (* special case for first chunk, which doesn't need an application
     symbol *)
  let first_args, first_handle, n_args, app_l, m, chunks' =
    match chunks with
    | [] -> assert false
    | (args, remaining_args) :: chunks' ->
        (* first application: no app symbol, only the function itself *)
        let handle =
          handle_arrow_l remaining_args (H_leaf ty_ret)
          |> ty_of_handle_ ~state |> handle_leaf in
        (* initial stack of applications *)
        let arity = List.length args in
        let app_l = [TC_first_param (id, arity)] in
        let m = IntMap.singleton (List.length args) app_l in
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
            [handle :=  args -> (remaining_args to ty_ret)] *)
        let handle_ret = handle_arrow_l remaining_args (H_leaf ty_ret) in
        let args' = ty_of_handle_ ~state prev_handle :: args in
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
    (fun k->k ID.print id pp_fun_encoding m);

  let fe = {
    fe_stack=m;
    fe_args=first_args;
    fe_ret_handle=first_handle;
  } in

  state.decode.fun_encodings <- ID.Map.add id fe state.decode.fun_encodings;
  fe

(* obtain or compute the fun encoding for [id] *)
let fun_encoding_for ~state id =
  try ID.Map.find id state.decode.fun_encodings
  with Not_found -> introduce_apply_syms ~state id

let sc_arity_ = function
  | TC_first_param (_,n) -> n
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
  encode_ty_ ~state (U.eval_renaming ~subst ty)

(* new type of the function that has this encoding *)
let ty_of_fun_encoding_ ~state fe =
  U.ty_arrow_l fe.fe_args (ty_of_handle_ ~state fe.fe_ret_handle)

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
        begin match T.repr f with
        | TI.Const id when ID.Map.mem id state.arities ->
            let l = List.map (aux subst Pol.NoPol) l in
            (* replace by applications symbols, based on [length l] *)
            let n = List.length l in
            let fun_encoding = fun_encoding_for ~state id in
            (* stack of application functions to use *)
            let app_l = IntMap.find n fun_encoding.fe_stack in
            apply_app_funs_ app_l (f::l)
        | TI.Var v when ID.Map.mem (Var.id v) state.arities ->
            let l = List.map (aux subst Pol.NoPol) l in
            let f' = U.var (Subst.find_exn ~subst v) in
            let fun_encoding = fun_encoding_for ~state (Var.id v) in
            let n = List.length l in
            let app_l = IntMap.find n fun_encoding.fe_stack in
            apply_app_funs_ app_l (f' :: l)
        | _ -> aux' subst pol t
        end
    | TI.Bind ((`Forall | `Exists) as b, v, _) when var_is_ho_ v ->
      begin match b, pol with
        | `Forall, Pol.Neg
        | `Exists, Pol.Pos -> aux' subst pol t  (* ok *)
        | _, Pol.NoPol ->
          (* aww. no idea, just avoid this branch if possible *)
          let res = U.asserting U.false_ [U.false_] in
          Utils.debugf ~section 3
            "@[<2>encode `@[%a@]`@ as `@[%a@]``,@ \
             quantifying over type `@[%a@]`@]"
            (fun k->k P.print t P.print res P.print (Var.ty v));
          state.lost_completeness <- true;
          res
        | `Forall, Pol.Pos
        | `Exists, Pol.Neg ->
          (* approximation required: we can never evaluate `forall v. t` *)
          let res = if pol=Pol.Neg then U.true_ else U.false_ in
          Utils.debugf ~section 3
            "@[<2>encode `@[%a@]`@ as `@[%a@]`,@ quantifying over type `@[%a@]`@]"
            (fun k->k P.print t P.print res P.print (Var.ty v));
          state.lost_completeness <- true;
          res
      end
    | TI.Builtin (`Eq (a,_)) when ty_is_ho_ (ty_term_ ~state a) ->
      (* higher-order comparison --> requires approximation *)
      begin match pol with
        | Pol.Neg -> aux' subst pol t (* fine *)
        | Pol.NoPol ->
          (* [a = b asserting has_proto a] *)
          let res = U.asserting t [U.false_] in
          Utils.debugf ~section 3
            "@[<2>encode HO equality `@[%a@]`@ as `@[%a@]`@]"
            (fun k->k P.print t P.print res);
          state.lost_completeness <- true;
          res
        | Pol.Pos ->
          (* [a = b && has_proto a] *)
          let res = U.false_ in
          Utils.debugf ~section 3
            "@[<2>encode HO equality `@[%a@]`@ as `@[%a@]`@]"
            (fun k->k P.print t P.print res);
          state.lost_completeness <- true;
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
    encode_ty_ ~state (U.eval_renaming ~subst ty)
  in
  aux subst pol t

(* given a (function) type, encode its arguments and return type but
   keeps the toplevel arrows *)
let encode_toplevel_ty ~state ty =
  let tyvars, args, ret = U.ty_unfold ty in
  assert (tyvars=[]);
  let args = List.map (encode_ty_ ~state) args in
  let ret = encode_ty_ ~state ret in
  U.ty_arrow_l args ret

(* OH MY.
   safe, because we only change the invariants *)
let cast_stmt_unsafe_ :
  (term, ty, inv1) Stmt.t -> (term, ty, inv2) Stmt.t = Obj.magic
let cast_rec_unsafe_ :
  (term, ty, inv1) Stmt.rec_def -> (term, ty, inv2) Stmt.rec_def = Obj.magic

(* translate a "single rec" into an "app rec" *)
let elim_hof_rec ~info ~state (defs:(_,_,inv1) Stmt.rec_defs)
: (_, _, inv2) Stmt.t list
=
  let elim_eqn
    : (term,ty,inv1) Stmt.rec_def -> (term,ty,inv2) Stmt.rec_def
    = fun def ->
      let id = def.Stmt.rec_defined.Stmt.defined_head in
      match def.Stmt.rec_eqns with
      | Stmt.Eqn_single (vars, rhs) ->
          if ID.Map.mem id state.arities then (
            (* higher-order function *)
            let fe = introduce_apply_syms ~state id in
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
                (function TC_first_param _ -> id | TC_app  a -> a.af_id) stack in
            let eqn = Stmt.Eqn_app (app_l, vars, lhs, rhs) in
            let defined = { Stmt.
              defined_head=id;
              defined_ty=ty_of_fun_encoding_ ~state fe;
            } in
            { Stmt.
              rec_defined=defined;
              rec_vars=vars;
              rec_eqns=eqn;
            }
          ) else (
            Utils.debugf ~section 5
              "@[<2>keep structure of FO def of `%a`@]" (fun k->k ID.print id);
            let tr_term subst = elim_hof_term ~state subst (ID.polarity id) in
            let tr_type _subst ty = encode_toplevel_ty ~state ty in
            Stmt.map_rec_def_bind Subst.empty def
              ~bind:(bind_hof_var ~state) ~term:tr_term ~ty:tr_type
            |> cast_rec_unsafe_
          )
  in
  let defs = List.map elim_eqn defs in
  [Stmt.axiom_rec ~info defs]

(* eliminate partial applications in the given statement. Can return several
   statements because of the declarations of new application symbols. *)
let elim_hof_statement ~state stmt : (_, _, inv2) Stmt.t list =
  let info = Stmt.info stmt in
  let tr_term pol subst = elim_hof_term ~state subst pol in
  let tr_type _subst ty = encode_toplevel_ty ~state ty in
  Utils.debugf ~section 3 "@[<2>@{<cyan>> elim HOF in stmt@}@ `@[%a@]`@]" (fun k->k PStmt.print stmt);
  (* find the new type of the given partially applied function [id : ty] *)
  let encode_fun id =
    Utils.debugf ~section 3
      "introduce application symbols and handle types for %a…"
      (fun k->k ID.print id);
    let fun_encoding = introduce_apply_syms ~state id in
    let ty' =
      U.ty_arrow_l fun_encoding.fe_args
        (ty_of_handle_ ~state fun_encoding.fe_ret_handle) in
    Utils.debugf ~section 4 "@[<2>fun %a now has type `@[%a@]`@]"
      (fun k->k ID.print id P.print ty');
    ty'
  in
  let stmt' = match Stmt.view stmt with
  | Stmt.Decl (id,ty,attrs) ->
      let ty' =
        if ID.Map.mem id state.arities
        then encode_fun id
        else encode_toplevel_ty ~state ty
            (* keep as is, not a partially applied fun; still have to modify type *)
      in
      [Stmt.decl ~info id ty' ~attrs]
  | Stmt.Axiom (Stmt.Axiom_rec l) -> elim_hof_rec ~state ~info l
  | Stmt.Axiom (Stmt.Axiom_spec spec) ->
      let subst, vars =
        Utils.fold_map (bind_hof_var ~state) Subst.empty spec.Stmt.spec_vars
      in
      let spec =
        { Stmt.
          spec_axioms=List.map (tr_term Pol.Pos subst) spec.Stmt.spec_axioms;
          spec_vars=vars;
          spec_defined=
            List.map
              (fun d ->
                 let id = Stmt.id_of_defined d in
                 let ty = Stmt.ty_of_defined d in
                 let ty' =
                   if ID.Map.mem id state.arities
                   then encode_fun id
                   else encode_toplevel_ty ~state ty
                 in
                 Stmt.mk_defined id ty')
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
                        cstor_args=List.map (encode_ty_ ~state) c.cstor_args;
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
      let copy_of = encode_ty_ ~state c.Stmt.copy_of in
      let copy_to = encode_ty_ ~state c.Stmt.copy_to in
      let c' = {
        c with Stmt.
          copy_pred = CCOpt.map (tr_term Pol.NoPol subst) c.Stmt.copy_pred;
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
          ~bind:(bind_hof_var ~state) ~term:(tr_term Pol.Pos) ~ty:tr_type
        |> cast_stmt_unsafe_ (* XXX: hack, but shorter *)
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
  let pb' = Problem.flat_map_statements pb ~f:(elim_hof_statement ~state) in
  let pb' =
    if state.lost_completeness
    then Problem.set_unsat_means_unknown pb'
    else pb'
  in
  (* return new problem *)
  pb', state.decode

(** {2 Decoding} *)

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
  | TI.Var v ->
    begin
      try Subst.find_exn ~subst v
      with Not_found ->
        errorf_ "could not find `%a` in subst %a"
          Var.print_full v (Subst.print P.print) subst
    end
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
  let open CCOpt.Infix in
  (* search in both functions and constants *)
  let res =
    CCList.find_map
      (fun (f,vars,dt,k) -> match T.repr f with
         | TI.Const id' when ID.equal id id' -> Some (vars,dt,k)
         | _ -> None)
      m.Model.funs
    <+>
    CCList.find_map
      (fun (t,u,k) -> match T.repr t with
         | TI.Const id' when ID.equal id id' -> Some ([], Model.DT.yield u, k)
         | _ -> None)
      m.Model.constants
  in
  match res with
    | None -> errorf_ "could not find model for function %a" ID.print id
    | Some tup -> tup

let as_var_ t = match T.repr t with
  | TI.Var v -> v
  | _ -> errorf_ "@[expected var, got term `@[%a@]`@]" P.print t

(* subst(var->term) -> var -> var
   we expect the variable to be mapped to another variable *)
let find_as_var_ ~subst v =
  try Subst.find_exn ~subst v |> as_var_
  with Not_found ->
    errorf_ "@[<2>could not find var %a in @[%a@]@ when decoding@]"
      Var.print_full v (Subst.print P.print) subst

(* filter [dt], keeping only the cases where [v=c] holds
   @param add_eqns list of tests to add to surviving cases *)
let filter_dt ?(add_eqns=[]) ~subst v c tests =
  (* does [v = c] in [eqns]? *)
  let maps_to v c ~in_:eqns =
    let subst = Subst.add ~subst v c in
    CCList.find_map
      (fun (v',t) ->
         if Var.equal v v'
         then if U.equal_with ~subst t c
           then Some true
           else Some false
         else None)
      eqns
    |> CCOpt.get true  (* if [v] does not occur, then [true] *)
  and remove_var v ~from:eqns =
    List.filter (fun (v',_) -> not (Var.equal v v')) eqns
  in
  CCList.filter_map
    (fun (eqns, rhs) ->
       if maps_to v c ~in_:eqns
       then (
         let eqns = remove_var v ~from:eqns in
         let eqns = add_eqns @ eqns in
         Some (eqns, rhs)
       ) else None)
    tests

let tr_eqns ~state ~map ~subst =
  List.map (fun (v,t) -> find_as_var_ ~subst v, decode_term ~state ~map subst t)

(* simple translation of a list of tests *)
let tr_tests ~state ~map ~subst =
  List.map
    (fun (eqns, rhs) ->
       let eqns = tr_eqns ~state ~map ~subst eqns in
       let rhs = decode_term ~state ~map subst rhs in
       eqns,rhs)

(* [t1] is a tree returning some handle type, and [t2] is a tree whose first
   variable ([remove_var]) has this exact handle type *)
let join_dt_ ~subst ~remove_var:v t1 t2 =
  let module DT = Model.DT in
  (* tests resulting from each case of [t1.tests] *)
  let tests1 =
    t1.DT.tests
    |> CCList.flat_map
      (fun (eqns, rhs) ->
         (* keep branches of [t2] that map [v] to [rhs] *)
         filter_dt ~add_eqns:eqns ~subst v rhs t2.DT.tests)
  (* tests corresponding to [t2.tests] in the case [v = t1.else_] *)
  and tests2 =
    let t = t1.DT.else_ in
    filter_dt ~subst v t t2.DT.tests
  and else_ =
    t2.DT.else_
  in
  DT.test_flatten (tests1 @ tests2) ~else_:(DT.yield else_)

(* translate a DT and returns a substitution with fresh variables *)
let tr_dt ~state ~map ~subst ?remove_var dt =
  Utils.debugf ~section 5 "@[<2>decode `@[%a@]`@ in @[%a@]@]"
    (fun k->k
        (Model.DT.print P.print) dt (Subst.print P.print) subst);
  let tr_ = decode_term ~state ~map subst in
  let dt : _ Model.DT.t =
    Model.DT.map dt
      ~var:(fun v -> match remove_var with
        | Some v' when Var.equal v v' -> None
        | _ -> Some (find_as_var_ ~subst v))
      ~term:tr_ ~ty:tr_ in
  dt

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

(* handle -> decoded type *)
let decode_handle ~state ~map h : ty =
  let tr_ty = decode_term ~state ~map Subst.empty in
  let rec aux h = match h with
    | H_leaf a -> tr_ty a
    | H_arrow (a,b) -> U.ty_arrow (tr_ty a) (aux b)
  in
  aux h

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
          List.fold_left (fun m i -> ID.Map.add i (ty,h) m) m ids)

let new_fun_name_ ~state =
  let id = ID.make_f "$$anon_fun_%d" state.dst_gensym in
  state.dst_gensym <- state.dst_gensym + 1;
  id

(* compute a map from constants of type "to a (to b c)" to fresh names
   of type "a -> b -> c", defined on the side.
  @return the map, and a list of definitions *)
let map_ho_consts_to_funs ~state m : const_map * (unit -> _ Model.fun_def list) =
  let const_tbl : T.t ID.Tbl.t = ID.Tbl.create 16 in
  let fun_defs : _ Model.fun_def list ref = ref [] in
  let all_fun_const = all_fun_consts_ ~state m in
  (* find the function corresponding to
     the constant [c] of type [to 'a (to 'b 'c)];
     @param app the application symbol corresponding to [to 'a (to 'b 'c)]
     @param ty the decoded (arrow) type ['a -> 'b -> 'c] *)
  let rec tr_functional_cst app ty c = match ID.Tbl.get const_tbl c with
    | Some t -> t
    | None ->
      Utils.debugf ~section 5
        "@[<2>tr fun constant `@[%a@] : @[%a@]`@ with app symbol `%a`@]"
        (fun k->k ID.print c P.print ty ID.print app);
      let _, _args, ret = U.ty_unfold ty in
      (* fixpoint *)
      let c' = new_fun_name_ ~state in
      ID.Tbl.add const_tbl c (U.const c');
      (* compute the body of the lambda *)
      let vars, dt = compute_dt app c c' in
      let t' = U.const c' in
      let module DTU = Model.DT_util(T) in
      let k = if U.ty_is_Prop ret then Model.Symbol_prop else Model.Symbol_fun in
      CCList.Ref.push fun_defs (t', vars, dt, k);
      Utils.debugf ~section 5
        "@[... decode `%a`@ into `@[@[%a %a@]@ := @[%a@]@]`@]"
        (fun k->k ID.print c ID.print c'
            (CCFormat.list Var.print_full) vars (Model.DT.print P.print) dt);
      t'
  (* compute a decision tree for this constant *)
  and compute_dt app c c' =
    let vars', dt, _ = find_dt_ m app in
    let v1, other_vars = match vars' with [] -> assert false | x::y -> x,y in
    (* rename [other_vars] *)
    let subst, vars =
      Utils.fold_map
        (bind_decode_var_ ~state ~map:map_id)
        Subst.empty other_vars
    in
    let subst' = Subst.add ~subst v1 (U.const c') in
    (* keep only the part of the DT corresponding to [v1=c] *)
    let tests =
      filter_dt ~subst v1 (U.const c) dt.Model.DT.tests
      |> tr_tests ~state ~map:map_id ~subst:subst'
    and else_ =
      decode_term ~state ~map:map_id subst' dt.Model.DT.else_ in
    vars, Model.DT.test tests ~else_
  (* if [id] is a domain constant, then map it to a lambda term,
    otherwise keep it intact *)
  and map_id
    : const_map
    = fun id -> match ID.Map.get id all_fun_const with
    | None -> U.const id
    | Some (ty,h) ->
      (* find corresponding apply symbol *)
      let h' = handle_arrow_l [ty] h in
      let app =
        try
          HandleMap.find_exn h' state.app_symbols
        with Not_found ->
          errorf_ "cannot find app symbol for `@[%a@],@ handle %a,@ full handle %a`"
            ID.print id pp_handle h pp_handle h'
      in
      let ty' = decode_handle ~state ~map:map_id h in
      tr_functional_cst app.af_id ty' id
  in
  map_id, (fun () -> !fun_defs)

(* Assuming [f_id = f_const] is a part of the model [m], and [f_id] is
   a function encoded using [tower], find the actual value of [f_id] in
   the model [m] by flattening/filtering discrimination trees for functions
   of [tower].
   @return set of variables, discrimination tree, function kind *)
let extract_subtree_ ~state ~map m tower =
  Utils.debugf ~section 5 "@[<2>extract subtree for @[%a@]@]" (fun k->k pp_fe_tower tower);
  let rename_decode_var = bind_decode_var_ ~state ~map in
  (* @param hd: first parameter, that is, the partial function being applied *)
  let rec aux subst hd tower = match tower with
    | [] -> assert false
    | TC_first_param _ :: _ -> assert false
    | [TC_app af] ->
        begin match find_dt_ m af.af_id with
          | [], _, _ -> assert false  (* af: must be a function *)
          | v::vars, dt, k ->
            let subst, _ = rename_decode_var subst v in
            let subst, vars = Utils.fold_map rename_decode_var subst vars in
            v, vars, subst, dt, k
        end
    | TC_app af :: tower' ->
        (* find and transform [dt] for [f] *)
        let vars, dt, _ = find_dt_ m af.af_id in
        (* first variable, [v], is replaced by [hd] *)
        let v, vars = match vars with a::b ->a,b | [] -> assert false in
        let subst = Subst.add ~subst v hd in
        let subst, vars = Utils.fold_map rename_decode_var subst vars in
        let hd = U.app hd (List.map U.var vars) in
        (* merge with [dt] for remaining tower functions *)
        let _, vars', subst, dt', k = aux subst hd tower' in
        let new_dt = join_dt_ ~remove_var:v ~subst dt dt' in
        v, vars @ vars', subst, new_dt, k
  in
  match tower with
    | []
    | TC_app _ ::_ -> assert false
    | TC_first_param (f,_) :: tower' ->
        let vars, dt, _ = find_dt_ m f in
        let subst, vars = Utils.fold_map rename_decode_var Subst.empty vars in
        (* in the surrounding application symbols, replace first arg with [hd] *)
        let hd = U.app_const f (List.map U.var vars) in
        (* merge with rest of DT *)
        let v, vars', subst, dt', k = aux subst hd tower' in
        let new_dt = join_dt_ ~subst ~remove_var:v dt dt' in
        vars @ vars', subst, new_dt, k

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
      ID.Map.find id state.fun_encodings
      |> (fun fe -> fe.fe_stack)
      |> IntMap.max_binding
      |> snd
    in
    let vars, subst, dt, k = extract_subtree_ ~state ~map m tower in
    let dt = tr_dt ~state ~map ~subst dt in
    Model.add_fun new_m (U.const id, vars, dt, k)
  in
  Model.fold (Model.empty_copy m) m
    ~finite_types:(fun new_m (ty,cases) ->
      match T.repr ty, state.dst_handle_id with
        | TI.Const id, Some id' when ID.equal id id' -> new_m (* drop handle type *)
        | _ when is_handle_ ~state ty -> new_m (* drop handle types *)
        | _ -> Model.add_finite_type new_m (tr_term ty) cases)
    ~constants:(fun new_m (t,u,k) ->
      match T.repr t with
        | TI.Const id when ID.Map.mem id state.fun_encodings ->
            decode_partial_fun_ new_m id
        | _ ->
            Model.add_const new_m (tr_term t, tr_term u, k))
    ~funs:(fun new_m (f,vars,dt,k) ->
      match T.repr f with
        | TI.Const id when ID.Tbl.mem state.dst_app_symbols id ->
            new_m (* drop application symbols from model *)
        | TI.Const id when ID.Map.mem id state.fun_encodings ->
            decode_partial_fun_ new_m id
        | _ ->
            let subst, vars =
              Utils.fold_map (bind_decode_var_ ~state ~map) Subst.empty vars in
            let dt = tr_dt ~state ~map ~subst dt in
            Model.add_fun new_m (tr_term f, vars, dt, k))
  |> (fun m -> List.fold_left Model.add_fun m (new_funs ()))

(** {2 Pipe} *)

let pipe_with ?on_decoded ~decode ~print ~check =
  let on_encoded =
    Utils.singleton_if print () ~f:(fun () ->
      let module PPb = Problem.Print(P)(P) in
      Format.printf "@[<v2>@{<Yellow>after elimination of HOF@}: %a@]@." PPb.print)
    @
    Utils.singleton_if check () ~f:(fun () ->
      let module C = TypeCheck.Make(T) in
      C.check_problem ?env:None)
  in
  Transform.make
    ?on_decoded
    ~on_encoded
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
         (Problem.Res.print P.print P.print)]
    else []
  in
  let decode state = Problem.Res.map_m ~f:(decode_model ~state) in
  pipe_with ~on_decoded ~print ~decode ~check
