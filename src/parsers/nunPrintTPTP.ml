
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(* {1 TPTP Printer}

   See http://www.cs.miami.edu/~tptp/TPTP/QuickGuide/FiniteInterpretations.html *)

open Nunchaku_core

module TI = TermInner
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

let pp_list ~sep p = CCFormat.list ~start:"" ~stop:"" ~sep p

module Make(T : TI.S) = struct
  module U = TI.Util(T)
  module P = TI.Print(T)

  type term = T.t
  type form = T.t
  type ty = T.t
  type model = (term, ty) Model.t

  let print_builtin print_inner out : term TI.Builtin.t -> unit = function
    | `True -> CCFormat.string out "$true"
    | `False -> CCFormat.string out "$false"
    | `Eq (a,b) ->
        fpf out "@[<hv>%a =@ %a@]" print_inner a print_inner b
    | `Equiv (a,b) ->
        fpf out "@[<hv>%a <=>@ %a@]" print_inner a print_inner b
    | `Undefined (_id,t) -> print_inner out t
    | `Not f -> fpf out "~ %a" print_inner f
    | `And l ->
        fpf out "@[<hv>%a@]" (pp_list ~sep:" & " print_inner) l
    | `Or l ->
        fpf out "@[<hv>%a@]" (pp_list ~sep:" | " print_inner) l
    | `Imply (a,b) ->
        fpf out "@[<hv>%a =>@ %a@]" print_inner a print_inner b
    | `DataTest _
    | `DataSelect _
    | `Guard _
    | `Unparsable _
    | `Ite _ -> assert false (* TODO *)

  (* disambiguate IDs when printing them *)
  let erase_state = ID.Erase.create_state()

  let id_to_name id = ID.Erase.to_name erase_state id

  let print_var out v = CCFormat.string out (Var.id v |> id_to_name)

  let rec print_term out t = match T.repr t with
    | TI.Var v -> print_var out v
    | TI.Bind (`Fun,v,t) ->
        fpf out "@[<2>^[%a]:@ %a@]" print_typed_var v print_inner t
    | TI.Bind (`Mu,_,_) -> Utils.not_implemented "print mu in TPTP"
    | TI.Let _ -> Utils.not_implemented "print let in TPTP"
    | TI.Match _ -> Utils.not_implemented "print match in TPTP"
    | TI.Builtin (`Unparsable _) -> error_ "cannot print `unparsable` in TPTP"
    | TI.Builtin (`Ite (a,b,c)) ->
        fpf out "$ite_t(@[<hv>%a,@ %a,@ %a@])"
          print_term a print_term b print_term c
    | TI.Bind (`Forall, v,t) ->
        fpf out "@[<2>![%a]:@ %a@]" print_typed_var v print_inner t
    | TI.Bind (`Exists, v,t) ->
        fpf out "@[<2>?[%a]:@ %a@]" print_typed_var v print_inner t
    | TI.TyArrow (a,b) ->
        fpf out "@[<2>%a >@ %a@]" print_inner a print_ty b
    | TI.Bind (`TyForall, v,t) ->
        fpf out "@[<2>!>[%a]:@ %a@]" print_var v print_inner t
    | TI.Const c -> CCFormat.string out (id_to_name c)
    | TI.App (_, []) -> assert false
    | TI.App (f, l) ->
        begin match T.repr f with
        | TI.Const _
        | TI.Var _ ->
            fpf out "@[<2>%a(%a)@]"
              print_inner f (pp_list ~sep:", " print_term) l
        | TI.Builtin _ -> assert false
        | _ ->
            Utils.not_implementedf
              "@[<2>print_model:@ could not apply `@[%a@]`@ to arguments [@[%a@]]@]"
              print_term f (pp_list ~sep:","P.print) l
        end
    | TI.TyMeta _ -> assert false
    | TI.Builtin b -> print_builtin print_inner out b
    | TI.TyBuiltin `Type -> CCFormat.string out "$tType"
    | TI.TyBuiltin `Kind -> error_ "cannot print `kind` in TPTP"
    | TI.TyBuiltin `Prop -> CCFormat.string out "$o"

  and print_ty out t = print_term out t
  and print_form out t = print_term out t

  and print_inner out t = match T.repr t with
    | TI.Var _
    | TI.TyMeta _
    | TI.TyBuiltin _
    | TI.Const _
    | TI.App (_,_)
    | TI.Let (_,_,_) -> print_term out t
    | TI.Builtin _
    | TI.Bind _
    | TI.Match _
    | TI.TyArrow (_,_) -> fpf out "(@[<2>%a@])" print_term t

  and print_typed_var out v = fpf out "%a:%a" print_var v print_ty (Var.ty v)

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
      errorf_ "variable %a should be in scope" Var.print v

  (* preprocess terms:
     - find and replace constants by "distinct" constants.
     - replace lower case (bound) variables by capitalized variables *)
  let rec preprocess_term ~state t = match T.repr t with
    | TI.Const id ->
        let id' =
          try ID.Tbl.find state.pre_constants id
          with Not_found -> id (* not a domain constant *)
        in
        U.const id'
    | TI.Var v ->
        let v' = find_var_ ~state v in
        U.var v'
    | TI.App (f,l) ->
        let f = preprocess_term ~state f in
        let l = List.map (preprocess_term ~state) l in
        U.app f l
    | TI.Bind (`Fun, v,t) ->
        preprocess_typed_var ~state v
          (fun v -> U.fun_ v (preprocess_term ~state t))
    | TI.Let (v,t,u) ->
        let t = preprocess_term ~state t in
        let u = preprocess_term ~state u in
        let v' = find_var_ ~state v in
        U.let_ v' t u
    | TI.Bind (`Mu, _,_) ->
        errorf_ "cannot represent `@[%a@]`@ in TPTP" P.print t
    | TI.Match _ -> Utils.not_implemented "replace in match"
    | TI.Builtin (`Ite (a,b,c)) ->
        let a = preprocess_term ~state a in
        let b = preprocess_term ~state b in
        let c = preprocess_term ~state c in
        U.ite a b c
    | TI.Bind (`Forall,v,t) ->
        preprocess_typed_var ~state v
          (fun v -> U.forall v (preprocess_term ~state t))
    | TI.Bind (`Exists,v,t) ->
        preprocess_typed_var ~state v
          (fun v -> U.exists v (preprocess_term ~state t))
    | TI.TyArrow (a,b) ->
        U.ty_arrow (preprocess_ty ~state a) (preprocess_ty ~state b)
    | TI.Bind (`TyForall,v,t) ->
        let v' = mk_var ~state v in
        U.ty_forall v' (preprocess_ty ~state t)
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
      | 'a' .. 'b' -> String.capitalize name
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

  (* translate [forall vars. t = dt] into a conjunction of cases *)
  let translate_dt kind vars t dt =
    let mk_subst tests =
      List.fold_left (fun subst (v,t) -> Var.Subst.add ~subst v t) Var.Subst.empty tests
    in
    (* turn each [test, rhs] into an equation or predicate *)
    let forms =
      List.rev_map
        (fun (tests, rhs) ->
          let subst = mk_subst tests in
          let args =
            List.map (fun v -> Var.Subst.find_or ~subst ~default:(U.var v) v) vars
          in
          let rhs = U.eval ~subst rhs in
          let body = match kind with
            | Model.Symbol_utype | Model.Symbol_data -> assert false
            | Model.Symbol_fun -> U.eq (U.app t args) rhs
            | Model.Symbol_prop ->
                (* propositions should become [p(x)] or [not p(x)] *)
                match T.repr rhs with
                | TI.Builtin `True -> U.app t args
                | TI.Builtin `False -> U.not_ (U.app t args)
                | _ -> U.equiv (U.app t args) rhs
          in
          U.forall_l vars body)
        (([], dt.Model.DT.else_) :: dt.Model.DT.tests)
    in
    U.and_ (List.rev forms)

  (* the domain declaration(s): [forall X:ty, (X=c1 | ... | X=cn)] where
     the [c_i] are the elements of [l] *)
  let mk_domain ty l =
    let v = Var.make ~ty ~name:"X" in
    let form =
      U.forall v
        (U.or_ (List.map (fun c -> U.eq (U.var v) (U.const c)) l))
    in
    { role=Role_domain; form; }

  let role_of_kind = function
    | Model.Symbol_prop -> Role_predicate
    | Model.Symbol_fun -> Role_functor
    | Model.Symbol_utype | Model.Symbol_data -> assert false

  (* preprocess model to make it as FO as possible, and associate it a role. *)
  let preprocess_model (m:model) : tptp_model =
    let state = create_state () in
    let res = CCVector.create () in
    (* finite types *)
    Sequence.of_list m.Model.finite_types
      |> Sequence.map
        (fun (ty,l) ->
          (* register domain constants *)
          List.iter (fun id -> ID.Tbl.add state.pre_constants id (mk_cst id)) l;
          let ty = preprocess_ty ~state ty in
          mk_domain ty l)
      |> CCVector.append_seq res;
    (* constants *)
    Sequence.of_list m.Model.constants
      |> Sequence.map
        (fun (t,u,k) ->
          let t = preprocess_term ~state t in
          let u = preprocess_term ~state u in
          { role = role_of_kind k; form = U.eq t u; })
      |> CCVector.append_seq res;
    (* functions *)
    Sequence.of_list m.Model.funs
      |> Sequence.map
        (fun (t,vars,dt,k) ->
          let module DT_U = Model.DT_util(T) in
          let form =
            preprocess_typed_vars ~state vars
              (fun vars -> translate_dt k vars t dt)
          in
          { role = role_of_kind k; form; })
      |> CCVector.append_seq res;
    CCVector.freeze res

  (* print a model *)
  let print_model out (m:model) =
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
      fpf out "@[<2>fof(%s, %a,@ @[%a@]).@]" name pp_role role print_form form
    in
    let header = "% --------------- begin TPTP model ------------"
    and footer = "% --------------- end TPTP model --------------" in
    Utils.debug ~section 3 "preprocess model...";
    let m' = preprocess_model m in
    fpf out "@[<v>%s@,%a@,%s@]"
      header (CCVector.print ~start:"" ~stop:"" ~sep:"" pp_stmt) m' footer
end
