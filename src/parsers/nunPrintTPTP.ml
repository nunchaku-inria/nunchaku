
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(* {1 TPTP Printer} *)

module A = NunUntypedAST
module M = NunProblem.Model
module Var = NunVar
module ID = NunID

type 'a printer = Format.formatter -> 'a -> unit

type term = NunUntypedAST.term
type form= NunUntypedAST.term
type model = term NunProblem.Model.t

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
              fpf out "@[<hv2>%a@]" (pp_list ~sep:" & " print_inner) l
          | A.Builtin.Or, _ ->
              fpf out "@[<hv2>%a@]" (pp_list ~sep:" | " print_inner) l
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
  | A.App (_,_)
  | A.Ite (_,_,_)
  | A.Let (_,_,_) -> print_term out t
  | A.Fun (_,_)
  | A.Forall (_,_)
  | A.Exists (_,_)
  | A.TyArrow (_,_)
  | A.TyForall (_,_) -> fpf out "(@[%a@])" print_term t

and print_var out v = CCFormat.string out v

and print_tyvar out (v,tyopt) = match tyopt with
  | None -> print_var out v
  | Some ty -> fpf out "%a:%a" print_var v print_ty ty

(* TODO: gather the set of constants and declare fi_domain on them *)
(* TODO: try to flatten, apply lamdabs to variables, unroll ITE...
  also annotate whether it's fi_functors or fi_predicates *)

(* preprocess model to make it as FO as possible *)
let preprocess_model m =
  CCList.flat_map
    (fun (t,u) ->
      [ t,u ]
    ) m

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
  let pp_pair out (t,u) =
    let name = mk_name "nun_model" in
    fpf out "@[<2>fof(%s, fi_functors,@ @[%a =@ %a@]).@]"
      name print_term t print_term u
  in
  let header = "% --------------- begin TPTP model ------------"
  and footer = "% --------------- end TPTP model --------------" in
  NunUtils.debugf ~section 3 "preprocess model..." (fun k -> k);
  let m = preprocess_model m in
  fpf out "@[<v>%s@,%a@,%s@]"
    header (pp_list ~sep:"" pp_pair) m footer

