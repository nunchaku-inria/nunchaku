
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(* {1 TPTP Printer}

   See http://www.cs.miami.edu/~tptp/TPTP/QuickGuide/FiniteInterpretations.html *)

open Nunchaku_core

module TI = TermInner
module T = Term
module M = Model

type 'a printer = Format.formatter -> 'a -> unit

let fpf = Format.fprintf
let section = Utils.Section.make "print_tptp"

exception Error of string

let () = Printexc.register_printer
    (function
      | Error msg -> Some (Utils.err_sprintf "in PrintTPTP:@ @[%s@]" msg)
      | _ -> None)

let error_ m = raise (Error m)
let errorf_ msg = CCFormat.ksprintf ~f:error_ msg

type role =
  | Role_functor
  | Role_predicate
  | Role_domain

let pp_role out = function
  | Role_functor -> CCFormat.string out "fi_functors"
  | Role_predicate -> CCFormat.string out "fi_predicates"
  | Role_domain -> CCFormat.string out "fi_domain"

let pp_list ~sep p = Utils.pp_list ~sep p

type term = T.t
type form = T.t
type ty = T.t
type model = (term, ty) Model.t

let pp_builtin pp_inner out : term Builtin.t -> unit = function
  | `True -> CCFormat.string out "$true"
  | `False -> CCFormat.string out "$false"
  | `Eq (a,b) ->
    fpf out "@[<hv>%a =@ %a@]" pp_inner a pp_inner b
  | `Undefined_atom _ -> error_ "cannot pp undefined atom"
  | `Undefined_self t -> pp_inner out t
  | `Not f -> fpf out "~ %a" pp_inner f
  | `And l ->
    fpf out "@[<hv>%a@]" (pp_list ~sep:" & " pp_inner) l
  | `Or l ->
    fpf out "@[<hv>%a@]" (pp_list ~sep:" | " pp_inner) l
  | `Imply (a,b) ->
    fpf out "@[<hv>%a =>@ %a@]" pp_inner a pp_inner b
  | `DataTest _
  | `DataSelect _
  | `Guard _
  | `Unparsable _
  | `Card_at_least _
  | `Ite _ -> assert false (* TODO *)

(* disambiguate IDs when printing them *)
let erase_state = ID.Erase.create_state()

let id_to_name id = ID.Erase.to_name erase_state id

let pp_var out v = CCFormat.string out (Var.id v |> id_to_name)

let rec pp_term out t = match T.repr t with
  | TI.Var v -> pp_var out v
  | TI.Bind (Binder.Fun,v,t) ->
    fpf out "@[<2>^[%a]:@ %a@]" pp_typed_var v pp_inner t
  | TI.Bind (Binder.Mu,_,_) -> Utils.not_implemented "print mu in TPTP"
  | TI.Let _ -> Utils.not_implemented "print let in TPTP"
  | TI.Match _ -> Utils.not_implemented "print match in TPTP"
  | TI.Builtin (`Unparsable _) -> error_ "cannot print `unparsable` in TPTP"
  | TI.Builtin (`Ite (a,b,c)) ->
    fpf out "$ite_t(@[<hv>%a,@ %a,@ %a@])"
      pp_term a pp_term b pp_term c
  | TI.Bind (Binder.Forall, v,t) ->
    fpf out "@[<2>![%a]:@ %a@]" pp_typed_var v pp_inner t
  | TI.Bind (Binder.Exists, v,t) ->
    fpf out "@[<2>?[%a]:@ %a@]" pp_typed_var v pp_inner t
  | TI.TyArrow (a,b) ->
    fpf out "@[<2>%a >@ %a@]" pp_inner a pp_ty b
  | TI.Bind (Binder.TyForall, v,t) ->
    fpf out "@[<2>!>[%a]:@ %a@]" pp_var v pp_inner t
  | TI.Const c -> CCFormat.string out (id_to_name c)
  | TI.App (_, []) -> assert false
  | TI.App (f, l) ->
    begin match T.repr f with
      | TI.Const _
      | TI.Var _ ->
        fpf out "@[<2>%a(%a)@]"
          pp_inner f (pp_list ~sep:", " pp_term) l
      | TI.Builtin _ -> assert false
      | _ ->
        Utils.not_implementedf
          "@[<2>print_model:@ could not apply `@[%a@]`@ to arguments [@[%a@]]@]"
          pp_term f (pp_list ~sep:","T.pp) l
    end
  | TI.TyMeta _ -> assert false
  | TI.Builtin b -> pp_builtin pp_inner out b
  | TI.TyBuiltin `Type -> CCFormat.string out "$tType"
  | TI.TyBuiltin `Kind -> error_ "cannot print `kind` in TPTP"
  | TI.TyBuiltin `Unitype -> CCFormat.string out "$i"
  | TI.TyBuiltin `Prop -> CCFormat.string out "$o"

and pp_ty out t = pp_term out t
and pp_form out t = pp_term out t

and pp_inner out t = match T.repr t with
  | TI.Var _
  | TI.TyMeta _
  | TI.TyBuiltin _
  | TI.Const _
  | TI.App (_,_)
  | TI.Let (_,_,_) -> pp_term out t
  | TI.Builtin _
  | TI.Bind _
  | TI.Match _
  | TI.TyArrow (_,_) -> fpf out "(@[<2>%a@])" pp_term t

and pp_typed_var out v = fpf out "%a:%a" pp_var v pp_ty (Var.ty v)

type tptp_statement = {
  role: role;
  form: form;
}

(* a model: a suite of statements *)
type tptp_model = tptp_statement CCVector.ro_vector

(* FIXME: still useful? *)
(* state used for preprocessing of models *)
type pre_state = {
  pre_constants: ID.t ID.Tbl.t; (* constant -> unique domain constants *)
  pre_vars: ty Var.t ID.Tbl.t; (* var->var *)
}

let create_state () =
  { pre_constants=ID.Tbl.create 16;
    pre_vars=ID.Tbl.create 16;
  }

(* create a domain constant *)
let mk_cst id =
  ID.make ("\"" ^ ID.name id ^ "\"")

let find_var_ ~state v =
  try ID.Tbl.find state.pre_vars (Var.id v)
  with Not_found ->
    errorf_ "variable %a should be in scope" Var.pp v

(* preprocess terms:
   - find and replace constants by "distinct" constants.
   - replace lower case (bound) variables by capitalized variables *)
let rec preprocess_term ~state t = match T.repr t with
  | TI.Const id ->
    let id' =
      try ID.Tbl.find state.pre_constants id
      with Not_found -> id (* not a domain constant *)
    in
    T.const id'
  | TI.Var v ->
    let v' = find_var_ ~state v in
    T.var v'
  | TI.App (f,l) ->
    let f = preprocess_term ~state f in
    let l = List.map (preprocess_term ~state) l in
    T.app f l
  | TI.Bind (Binder.Fun, v,t) ->
    preprocess_typed_var ~state v
      (fun v -> T.fun_ v (preprocess_term ~state t))
  | TI.Let (v,t,u) ->
    let t = preprocess_term ~state t in
    let u = preprocess_term ~state u in
    let v' = find_var_ ~state v in
    T.let_ v' t u
  | TI.Bind (Binder.Mu, _,_) ->
    errorf_ "cannot represent `@[%a@]`@ in TPTP" T.pp t
  | TI.Match _ -> Utils.not_implemented "replace in match"
  | TI.Builtin (`Ite (a,b,c)) ->
    let a = preprocess_term ~state a in
    let b = preprocess_term ~state b in
    let c = preprocess_term ~state c in
    T.ite a b c
  | TI.Bind (Binder.Forall,v,t) ->
    preprocess_typed_var ~state v
      (fun v -> T.forall v (preprocess_term ~state t))
  | TI.Bind (Binder.Exists,v,t) ->
    preprocess_typed_var ~state v
      (fun v -> T.exists v (preprocess_term ~state t))
  | TI.TyArrow (a,b) ->
    T.ty_arrow (preprocess_ty ~state a) (preprocess_ty ~state b)
  | TI.Bind (Binder.TyForall,v,t) ->
    let v' = mk_var ~state v in
    T.ty_forall v' (preprocess_ty ~state t)
  | TI.Builtin _ -> t
  | TI.TyBuiltin _
  | TI.TyMeta _ -> t

and preprocess_typed_var ~state v f =
  assert (not(ID.Tbl.mem state.pre_vars (Var.id v)));
  let v' = mk_var ~state v in
  ID.Tbl.add state.pre_vars (Var.id v') v';
  f v'

and preprocess_ty ~state t = preprocess_term ~state t

(* make a valid TPTP variable *)
and mk_var ~state v =
  let name = ID.name (Var.id v) in
  let name = match name.[0] with
    | 'A' .. 'Z' -> name
    | 'a' .. 'b' -> CCString.capitalize_ascii name
    | _ -> "V" ^ name
  in
  Var.make ~name ~ty:(preprocess_ty ~state (Var.ty v))

let preprocess_typed_vars ~state vars f =
  let rec aux acc vars f = match vars with
    | [] -> f (List.rev acc)
    | v :: vars' ->
      preprocess_typed_var ~state v
        (fun v' ->  aux (v'::acc) vars' f)
  in
  aux [] vars f

(* translate [forall vars. t = dt] into a conjunction of cases.
   @param vars the transformed version of [dt.vars] *)
let translate_dt kind ~vars t dt =
  let mk_subst tests =
    List.fold_left
      (fun subst {M.DT.ft_var=v; ft_term=t} -> Var.Subst.add ~subst v t)
      Var.Subst.empty tests
  in
  (* turn each [test, rhs] into an equation or predicate *)
  let fdt = M.DT.flatten dt in
  let forms =
    List.map
      (fun (tests, rhs) ->
         let subst = mk_subst tests in
         let args =
           List.map (fun v -> Var.Subst.find_or ~subst ~default:(T.var v) v) vars
         in
         let rhs = T.eval ~subst rhs in
         let body = match kind with
           | Model.Symbol_utype
           | Model.Symbol_data
           | Model.Symbol_codata -> assert false
           | Model.Symbol_fun -> T.eq (T.app t args) rhs
           | Model.Symbol_prop ->
             (* propositions should become [p(x)] or [not p(x)] *)
             match T.repr rhs with
               | TI.Builtin `True -> T.app t args
               | TI.Builtin `False -> T.not_ (T.app t args)
               | _ -> T.eq (T.app t args) rhs
         in
         T.forall_l vars body
      )
      fdt.M.DT.fdt_cases
  in
  T.and_ forms

(* the domain declaration(s): [forall X:ty, (X=c1 | ... | X=cn)] where
   the [c_i] are the elements of [l] *)
let mk_domain ty l =
  let v = Var.make ~ty ~name:"X" in
  let form =
    T.forall v
      (T.or_ (List.map (fun c -> T.eq (T.var v) (T.const c)) l))
  in
  { role=Role_domain; form; }

let role_of_kind = function
  | Model.Symbol_prop -> Role_predicate
  | Model.Symbol_fun -> Role_functor
  | Model.Symbol_utype | Model.Symbol_data | Model.Symbol_codata -> assert false

(* preprocess model to make it as FO as possible, and associate it a role. *)
let preprocess_model (m:model) : tptp_model =
  let state = create_state () in
  let res = CCVector.create () in
  (* finite types *)
  Model.finite_types m
  |> Iter.map
    (fun (ty,l) ->
       (* register domain constants *)
       List.iter (fun id -> ID.Tbl.add state.pre_constants id (mk_cst id)) l;
       let ty = preprocess_ty ~state ty in
       mk_domain ty l)
  |> CCVector.append_seq res;
  (* constants *)
  Model.values m
  |> Iter.map
    (fun (t,dt,k) ->
       let t = preprocess_term ~state t in
       let vars = M.DT.vars dt in
       let form =
         preprocess_typed_vars ~state vars
           (fun vars -> translate_dt k t ~vars dt)
       in
       { role = role_of_kind k; form; })
  |> CCVector.append_seq res;
  CCVector.freeze res

(* print a model *)
let pp_model out (m:model) =
  (* generate new names for TPTP statements *)
  let mk_name =
    let n = ref 0 in
    fun s ->
      let name = s ^ "_" ^ string_of_int !n in
      incr n;
      name
  in
  (* print a single component of the model *)
  let pp_stmt out {form; role; } =
    let name = mk_name "nun_model" in
    fpf out "@[<2>fof(%s, %a,@ @[%a@]).@]" name pp_role role pp_form form
  in
  let header = "% --------------- begin TPTP model ------------"
  and footer = "% --------------- end TPTP model --------------" in
  Utils.debug ~section 3 "preprocess model...";
  let m' = preprocess_model m in
  fpf out "@[<v>%s@,%a@,%s@]"
    header (Utils.pp_seq ~sep:"" pp_stmt) (CCVector.to_iter m') footer
