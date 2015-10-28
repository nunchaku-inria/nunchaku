
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(* {1 TPTP Printer} *)

module A = NunUntypedAST
module M = NunModel
module Var = NunVar
module ID = NunID

type 'a printer = Format.formatter -> 'a -> unit

type term = NunUntypedAST.term
type form= NunUntypedAST.term
type model = term M.t

let fpf = Format.fprintf
let section = NunUtils.Section.make "print_tptp"

let pp_list ~sep p = CCFormat.list ~start:"" ~stop:"" ~sep p

let rec print_term out t = match A.view t with
  | A.Wildcard  -> fpf out "$_"
  | A.Builtin b -> A.Builtin.print out b
  | A.AtVar v
  | A.Var v -> print_var out v
  | A.Fun (v,t) ->
      fpf out "@[<2>^[%a]:@ %a@]" print_tyvar v print_inner t
  | A.Let _ -> NunUtils.not_implemented "print let in TPTP"
  | A.Match _ -> NunUtils.not_implemented "print match in TPTP"
  | A.Ite (a,b,c) ->
      fpf out "$ite_t(@[<hv>%a,@ %a,@ %a@])"
        print_term a print_term b print_term c
  | A.Forall (v,t) ->
      fpf out "@[<2>![%a]:@ %a@]" print_tyvar v print_inner t
  | A.Exists (v,t) ->
      fpf out "@[<2>?[%a]:@ %a@]" print_tyvar v print_inner t
  | A.TyArrow (a,b) ->
      fpf out "@[<2>%a >@ %a@]" print_inner a print_ty b
  | A.TyForall (v,t) ->
      fpf out "@[<2>!>[%a]:@ %a@]" print_var v print_inner t
  | A.App (_, []) -> assert false
  | A.App (f, l) ->
      begin match A.view f with
      | A.Var _
      | A.AtVar _ ->
          fpf out "@[<2>%a(%a)@]"
            print_inner f (pp_list ~sep:", " print_term) l
      | A.Builtin b ->
          begin match b, l with
          | A.Builtin.True, [] -> fpf out "$true"
          | A.Builtin.False, [] -> fpf out "$false"
          | A.Builtin.Prop, [] -> fpf out "$o"
          | A.Builtin.Type, [] -> fpf out "$tType"
          | A.Builtin.Not, [f] -> fpf out "~ %a" print_inner f
          | A.Builtin.And, _ ->
              fpf out "@[<hv>%a@]" (pp_list ~sep:" & " print_inner) l
          | A.Builtin.Or, _ ->
              fpf out "@[<hv>%a@]" (pp_list ~sep:" | " print_inner) l
          | A.Builtin.Eq, [a;b] ->
              fpf out "@[<hv>%a =@ %a@]" print_inner a print_inner b
          | A.Builtin.Imply, [a;b] ->
              fpf out "@[<hv>%a =>@ %a@]" print_inner a print_inner b
          | A.Builtin.Equiv, [a;b] ->
              fpf out "@[<hv>%a <=>@ %a@]" print_inner a print_inner b
          | A.Builtin.Prop ,_
          | A.Builtin.Type ,_
          | A.Builtin.Not ,_
          | A.Builtin.True ,_
          | A.Builtin.False ,_
          | A.Builtin.Eq ,_
          | A.Builtin.Equiv ,_
          | A.Builtin.Imply ,_ -> assert false
          end
      | _ ->
          NunUtils.not_implementedf "could not apply %a to arguments" print_term f
      end
  | A.MetaVar _ -> assert false

and print_ty out t = print_term out t
and print_form out t = print_term out t

and print_inner out t = match A.view t with
  | A.Wildcard | A.Builtin _ | A.Var _ | A.AtVar _ | A.MetaVar _
  | A.Ite (_,_,_)
  | A.Let (_,_,_) -> print_term out t
  | A.App (f,_) ->
      begin match A.view f with
      | A.Builtin A.Builtin.And
      | A.Builtin A.Builtin.Or
      | A.Builtin A.Builtin.Imply
      | A.Builtin A.Builtin.Equiv
      | A.Builtin A.Builtin.Not ->
          fpf out "(@[<hv>%a@])" print_term t
      | _ -> print_term out t
      end
  | A.Fun (_,_)
  | A.Match _
  | A.Forall (_,_)
  | A.Exists (_,_)
  | A.TyArrow (_,_)
  | A.TyForall (_,_) -> fpf out "(@[<2>%a@])" print_term t

and print_var out v = CCFormat.string out v

and print_tyvar out (v,tyopt) = match tyopt with
  | None -> print_var out v
  | Some ty -> fpf out "%a:%a" print_var v print_ty ty

(* TODO: gather the set of constants and declare fi_domain on them *)
(* TODO: try to flatten, apply lamdabs to variables, unroll ITE...
  also annotate whether it's fi_functors or fi_predicates *)

module StrSet = Set.Make(String)

(* state used for preprocessing of models *)
type pre_state = {
  pre_bound: StrSet.t; (* bound vars *)
  pre_types: (string, unit) Hashtbl.t;  (* type constructors *)
  pre_constants: (string, A.term) Hashtbl.t; (* unique domain constants *)
  pre_in_ty : bool; (* in type? if yes, do not use distinct constants *)
}

let pre_state_create() =
  { pre_bound=StrSet.empty; pre_in_ty=false;
    pre_types=Hashtbl.create 16; pre_constants=Hashtbl.create 16; }
let pre_state_bind ~state v = {state with pre_bound=StrSet.add v state.pre_bound}
let pre_state_enter_ty ~state = {state with pre_in_ty=true }

(* preprocess model to make it as FO as possible, and associate it a role. *)
let preprocess_model m =
  let role_fun = "fi_functors" and _role_pred = "fi_predicates" in
  let mk_cst v = "\"" ^ v ^ "\"" in (* a domain constant *)
  (* make a valid TPTP variable *)
  let mk_var v = match v.[0] with
    | 'A' .. 'Z' -> v
    | 'a' .. 'b' -> String.capitalize v
    | _ -> "V" ^ v
  in
  (* find and replace constants by distinct constants.
    Also replace lower case (bound) variables by capitalized variables *)
  let rec find_cst_term ~state t = match A.view t with
    | A.Var v | A.MetaVar v | A.AtVar v ->
        if StrSet.mem v state.pre_bound then A.var (mk_var v)
        else if state.pre_in_ty || Hashtbl.mem state.pre_types v then (
          Hashtbl.replace state.pre_types v (); (* remember this is a type *)
          A.var v
        ) else (
          try Hashtbl.find state.pre_constants v
          with Not_found ->
            let v' = mk_cst v in
            Hashtbl.add state.pre_constants v (A.var v');
            A.var v'
        )
    | A.Wildcard
    | A.Builtin _ -> t
    | A.App (f,l) ->
        let f = find_cst_term ~state f in
        let l = List.map (find_cst_term ~state) l in
        A.app f l
    | A.Fun (v,t) ->
        aux_typed_var ~state v
          (fun state v -> A.fun_ v (find_cst_term ~state t))
    | A.Let (v,t,u) ->
        let t = find_cst_term ~state t in
        let u = find_cst_term ~state:(pre_state_bind ~state v) u in
        A.let_ (mk_var v) t u
    | A.Match _ -> NunUtils.not_implemented "replace in match"
    | A.Ite (a,b,c) ->
        let a = find_cst_term ~state a in
        let b = find_cst_term ~state b in
        let c = find_cst_term ~state c in
        A.ite a b c
    | A.Forall (v,t) ->
        aux_typed_var ~state v
          (fun state v -> A.forall v (find_cst_term ~state t))
    | A.Exists (v,t) ->
        aux_typed_var ~state v
          (fun state v -> A.exists v (find_cst_term ~state t))
    | A.TyArrow (a,b) ->
        A.ty_arrow (aux_ty ~state a) (aux_ty ~state b)
    | A.TyForall (v,t) ->
        A.ty_forall (mk_var v)
          (aux_ty ~state:(pre_state_bind ~state v) t)
  and aux_typed_var ~state (v,tyopt) f =
    let var = mk_var v, CCOpt.map (aux_ty ~state) tyopt in
    f (pre_state_bind ~state v) var
  and aux_ty ~state t =
    let state = pre_state_enter_ty ~state in
    find_cst_term ~state t
  (* the domain declaration(s): forall X, (X=c1 | ... | X=cn)
      TODO: one domain declaration per type! *)
  and mk_domain ~state =
    let l = Hashtbl.fold (fun _ c acc -> c::acc) state.pre_constants [] in
    let f =
      A.forall ("X", None)
        (A.or_ (List.map (fun c -> A.eq (A.var "X") c) l))
    in
    [ f, "fi_domain" ]
  in
  (* make formula(s) out of a pair t=u *)
  let return x = [x]
  and (>|=) l f = CCList.map f l
  and (>>=) l f = CCList.flat_map f l in
  let rec preprocess_pair ~state t u =
    match A.view u with
      | A.Wildcard | A.Builtin _ | A.Var _ | A.AtVar _ | A.MetaVar _
      | A.TyArrow (_,_) | A.TyForall (_,_)
      | A.App _ ->
          return (A.eq t u)
      | A.Fun ((v,_) as typed_v, u') ->
          preprocess_pair ~state (A.app t [A.var v]) u' >|= fun f ->
          A.forall typed_v f
      | A.Forall (v, u') ->
          preprocess_pair ~state t u' >|= fun f ->
          A.forall v f
      | A.Exists (v, u') ->
          preprocess_pair ~state t u' >|= fun f ->
          A.exists v f
      | A.Let (v,u1,u2) ->
          preprocess_pair ~state t u2 >|= fun u2 ->
          A.let_ v u1 u2
      | A.Ite (u1,u2,u3) ->
          preprocess_pair ~state t u2 >>= fun u2 ->
          preprocess_pair ~state t u3 >|= fun u3 ->
          A.ite u1 u2 u3
      | A.Match _ -> NunUtils.not_implemented "printTPTP: match"
  in
  let state = pre_state_create() in
  let m' = m
    >>= fun (t,u) ->
    let u = find_cst_term ~state u in
    preprocess_pair ~state t u
    >|= fun form ->
    let role = role_fun in
    form, role
  in
  let prelude = mk_domain ~state in
  prelude @ m'

(* print a model *)
let print_model out m =
  (* generate new names for TPTP statements *)
  let mk_name =
    let n = ref 0 in
    fun s ->
      let name = s ^ "_" ^ string_of_int !n in
      incr n;
      name
  in
  (* print a single component of the model *)
  let pp_form out (f,role) =
    let name = mk_name "nun_model" in
    fpf out "@[<2>fof(%s, %s,@ @[%a@]).@]" name role print_form f
  in
  let header = "% --------------- begin TPTP model ------------"
  and footer = "% --------------- end TPTP model --------------" in
  NunUtils.debugf ~section 3 "preprocess model..." (fun k -> k);
  let m = preprocess_model m in
  fpf out "@[<v>%s@,%a@,%s@]"
    header (pp_list ~sep:"" pp_form) m footer

