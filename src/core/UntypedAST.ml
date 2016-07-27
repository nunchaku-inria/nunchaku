
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Input AST} *)

module Loc = Location

exception ParseError of Loc.t
exception SyntaxError of string * Loc.t option

let () = Printexc.register_printer
  (function
    | ParseError loc -> Some ("parse error at " ^ Loc.to_string loc)
    | SyntaxError (msg, loc) ->
        Some (Printf.sprintf "syntax error: %s at %s" msg (Loc.to_string_opt loc))
    | _ -> None
  )

type var = string
type var_or_wildcard = [`Var of string | `Wildcard]

module Builtin : sig
  type t =
    [ `Prop
    | `Type
    | `Not
    | `And
    | `Or
    | `True
    | `False
    | `Eq
    | `Equiv
    | `Imply
    | `Undefined of string
    | `Unitype
    ]

  include Intf.PRINT with type t := t
  val fixity : t -> [`Prefix | `Infix]
  val to_string : t -> string
end = struct
  type t =
    [ `Prop
    | `Type
    | `Not
    | `And
    | `Or
    | `True
    | `False
    | `Eq
    | `Equiv
    | `Imply
    | `Undefined of string
    | `Unitype
    ]

  let fixity : t -> [`Infix | `Prefix] = function
    | `Type
    | `True
    | `False
    | `Prop
    | `Not -> `Prefix
    | `And
    | `Or
    | `Imply
    | `Equiv
    | `Eq
    | `Unitype
    | `Undefined _ -> `Infix

  let to_string : t -> string = function
    | `Type -> "type"
    | `Prop -> "prop"
    | `Not -> "~"
    | `And -> "&&"
    | `Or -> "||"
    | `True -> "true"
    | `False -> "false"
    | `Eq -> "="
    | `Equiv -> "="
    | `Imply -> "=>"
    | `Undefined s -> "?_" ^ s
    | `Unitype -> "<unitype>"

  let print out s = Format.pp_print_string out (to_string s)
end


type term = term_node Loc.with_loc
and term_node =
  | Builtin of Builtin.t
  | Var of var_or_wildcard
  | AtVar of var  (* variable without implicit arguments *)
  | MetaVar of var (* unification variable *)
  | App of term * term list
  | Fun of typed_var * term
  | Let of var * term * term
  | Match of term * (var * var_or_wildcard list * term) list
  | Ite of term * term * term
  | Forall of typed_var * term
  | Exists of typed_var * term
  | Mu of typed_var * term
  | TyArrow of ty * ty
  | TyForall of var * ty
  | Asserting of term * term list

(* we mix terms and types because it is hard to know, in
  [@cons a b c], which ones of [a, b, c] are types, and which ones
  are terms *)
and ty = term

(** A variable with, possibly, its type *)
and typed_var = var * ty option

let view = Loc.get

(* mutual definitions of symbols, with a type and a list of axioms for each one *)
type rec_defs = (string * term * term list) list

(* specification of symbols with their types, as a list of axioms *)
type spec_defs = (string * term) list * term list

(* list of mutual type definitions (the type name, its argument variables,
   and its constructors that are (id args) *)
type mutual_types = (var * var list * (var * ty list) list) list

(* list of mutual (co) inductive predicates definitions. Each definition
    is the predicate, its type, and a list of clauses defining it *)
type mutual_preds = (var * ty * term list) list

type copy = {
  id: var; (* the new name *)
  copy_vars: var list; (* type variables *)
  of_: term; (* the definition *)
  abstract: var; (* abstract function *)
  concrete: var; (* concrete function *)
  pred: term option; (* the predicate *)
}

type attribute = string list
(** one attribute = list of strings separated by spaces *)

type statement_node =
  | Include of string * (string list) option (* file, list of symbols *)
  | Decl of var * ty * attribute list (* declaration of uninterpreted symbol *)
  | Axiom of term list (* axiom *)
  | Spec of spec_defs (* spec *)
  | Rec of rec_defs (* mutual rec *)
  | Data of mutual_types (* inductive type *)
  | Codata of mutual_types
  | Def of string * term  (* a=b, simple def *)
  | Pred of [`Wf | `Not_wf] * mutual_preds
  | Copred of [`Wf | `Not_wf] * mutual_preds
  | Copy of copy
  | Goal of term (* goal *)

type statement = {
  stmt_loc: Loc.t option;
  stmt_name: string option;
  stmt_value: statement_node;
}

let wildcard ?loc () = Loc.with_loc ?loc (Var `Wildcard)
let builtin ?loc s = Loc.with_loc ?loc (Builtin s)
let var ?loc v = Loc.with_loc ?loc (Var (`Var v))
let at_var ?loc v = Loc.with_loc ?loc (AtVar v)
let meta_var ?loc v = Loc.with_loc ?loc (MetaVar v)
let rec app ?loc t l = match Loc.get t with
  | App (f, l1) -> app ?loc f (l1 @ l)
  | _ -> Loc.with_loc ?loc (App (t,l))
let fun_ ?loc v t = Loc.with_loc ?loc (Fun(v,t))
let let_ ?loc v t u = Loc.with_loc ?loc (Let (v,t,u))
let match_with ?loc t l = Loc.with_loc ?loc (Match (t,l))
let ite ?loc a b c = Loc.with_loc ?loc (Ite (a,b,c))
let ty_prop = builtin `Prop
let ty_type = builtin `Type
let true_ = builtin `True
let false_ = builtin `False
let not_ ?loc f = app ?loc (builtin ?loc `Not) [f]

(* apply [b], an infix operator, to [l], in an associative way *)
let rec app_infix_l ?loc f l = match l with
  | [] -> assert false
  | [t] -> t
  | a :: tl -> app ?loc f [a; app_infix_l ?loc f tl]

let and_ ?loc l = app_infix_l ?loc (builtin ?loc `And) l
let or_ ?loc l = app_infix_l ?loc (builtin ?loc `Or) l
let imply ?loc a b = app ?loc (builtin ?loc `Imply) [a;b]
let equiv ?loc a b = app ?loc (builtin ?loc `Equiv) [a;b]
let eq ?loc a b = app ?loc (builtin ?loc `Eq) [a;b]
let neq ?loc a b = not_ ?loc (eq ?loc a b)
let forall ?loc v t = Loc.with_loc ?loc (Forall (v, t))
let exists ?loc v t = Loc.with_loc ?loc (Exists (v, t))
let mu ?loc v t = Loc.with_loc ?loc (Mu (v,t))
let asserting ?loc t l = match l with
  | [] -> t
  | _::_ -> Loc.with_loc ?loc (Asserting (t,l))
let ty_arrow ?loc a b = Loc.with_loc ?loc (TyArrow (a,b))
let ty_forall ?loc v t = Loc.with_loc ?loc (TyForall (v,t))

let ty_forall_list ?loc = List.fold_right (ty_forall ?loc)
let ty_arrow_list ?loc = List.fold_right (ty_arrow ?loc)

let forall_list ?loc = List.fold_right (forall ?loc)
let exists_list ?loc = List.fold_right (exists ?loc)
let fun_list ?loc = List.fold_right (fun_ ?loc)

let forall_term = var "!!"
let exists_term = var "??"

let mk_stmt_ ?loc ?name st =
  {stmt_loc=loc; stmt_name=name; stmt_value=st }

let include_ ?name ?loc ?which f = mk_stmt_ ?name ?loc (Include(f,which))
let decl ?name ?loc ~attrs v t = mk_stmt_ ?name ?loc (Decl(v,t,attrs))
let axiom ?name ?loc l = mk_stmt_ ?name ?loc (Axiom l)
let spec ?name ?loc l = mk_stmt_ ?name ?loc (Spec l)
let rec_ ?name ?loc l = mk_stmt_ ?name ?loc (Rec l)
let def ?name ?loc a b = mk_stmt_ ?name ?loc (Def (a,b))
let data ?name ?loc l = mk_stmt_ ?name ?loc (Data l)
let codata ?name ?loc l = mk_stmt_ ?name ?loc (Codata l)
let pred ?name ?loc ~wf l = mk_stmt_ ?name ?loc (Pred (wf, l))
let copred ?name ?loc ~wf l = mk_stmt_ ?name ?loc (Copred (wf, l))
let copy ?name ?loc ~of_ ~abstract ~concrete ~pred id vars =
  mk_stmt_ ?name ?loc (Copy {id; copy_vars=vars; of_; abstract; concrete; pred })
let goal ?name ?loc t = mk_stmt_ ?name ?loc (Goal t)

let rec head t = match Loc.get t with
  | Var (`Var v) | AtVar v | MetaVar v -> v
  | Asserting (f,_)
  | App (f,_) -> head f
  | Var `Wildcard | Builtin _ | TyArrow (_,_)
  | Fun (_,_) | Let _ | Match _ | Ite (_,_,_)
  | Forall (_,_) | Mu _ | Exists (_,_) | TyForall (_,_) ->
      invalid_arg "untypedAST.head"

let fpf = Format.fprintf

let pp_var_or_wildcard out = function
  | `Var v -> CCFormat.string out v
  | `Wildcard -> CCFormat.string out "_"

let rec unroll_if_ t = match Loc.get t with
  | Ite (a,b,c) ->
      let l, last = unroll_if_ c in
      (a,b) :: l, last
  | _ -> [], t

let pp_list_ ~sep p = CCFormat.list ~start:"" ~stop:"" ~sep p

let rec print_term out term = match Loc.get term with
  | Builtin s -> Builtin.print out s
  | Var v -> pp_var_or_wildcard out v
  | AtVar v -> fpf out "@@%s" v
  | MetaVar v -> fpf out "?%s" v
  | App (f, [a;b]) ->
      begin match Loc.get f with
      | Builtin s when Builtin.fixity s = `Infix ->
          fpf out "@[<hv>%a@ @[<hv>%a@ %a@]@]"
            print_term_inner a Builtin.print s print_term_inner b
      | _ ->
          fpf out "@[<2>%a@ %a@ %a@]" print_term_inner f
            print_term_inner a print_term_inner b
      end
  | App (a, l) ->
      fpf out "@[<2>%a@ %a@]"
        print_term_inner a (pp_list_ ~sep:" " print_term_inner) l
  | Fun (v, t) ->
      fpf out "@[<2>fun %a.@ %a@]" print_typed_var v print_term t
  | Mu (v, t) ->
      fpf out "@[<2>mu %a.@ %a@]" print_typed_var v print_term t
  | Let (v,t,u) ->
      fpf out "@[<2>let %s :=@ %a in@ %a@]" v print_term t print_term u
  | Match (t,l) ->
      let pp_case out (id,vars,t) =
        fpf out "@[<hv2>| %s %a ->@ %a@]"
          id (pp_list_ ~sep:" " pp_var_or_wildcard) vars print_term t
      in
      fpf out "@[<hv2>match @[%a@] with@ %a end@]"
        print_term t (pp_list_ ~sep:"" pp_case) l
  | Ite (a,b,c) ->
      (* special case to avoid deep nesting of ifs *)
      let pp_middle out (a,b) =
        fpf out "@[<2>else if@ @[%a@]@]@ @[<2>then@ @[%a@]@]" print_term a print_term b
      in
      let middle, last = unroll_if_ c in
      fpf out "@[<hv>@[<2>if@ @[%a@]@]@ @[<2>then@ %a@]@ %a@ @[<2>else@ %a@]@]"
        print_term a print_term b
        (pp_list_ ~sep:"" pp_middle) middle
        print_term last
  | Forall (v, t) ->
      fpf out "@[<2>forall %a.@ %a@]" print_typed_var v print_term t
  | Exists (v, t) ->
      fpf out "@[<2>exists %a.@ %a@]" print_typed_var v print_term t
  | Asserting (_, []) -> assert false
  | Asserting (t, l) ->
      fpf out "@[<2>%a@ @[<2>asserting @[%a@]@]@]"
        print_term_inner t (pp_list_ ~sep:" && " print_term_inner) l
  | TyArrow (a, b) ->
      fpf out "@[<2>%a ->@ %a@]"
        print_term_in_arrow a print_term b
  | TyForall (v, t) ->
      fpf out "@[<2>pi %s:type.@ %a@]" v print_term t
and print_term_inner out term = match Loc.get term with
  | App _ | Fun _ | Let _ | Ite _ | Match _ | Asserting _
  | Forall _ | Exists _ | TyForall _ | Mu _ | TyArrow _ ->
      fpf out "(%a)" print_term term
  | Builtin _ | AtVar _ | Var _ | MetaVar _ -> print_term out term
and print_term_in_arrow out t = match Loc.get t with
  | Builtin _
  | Var _ | AtVar _ | MetaVar _
  | App (_,_) -> print_term out t
  | Let _ | Match _
  | Ite _
  | Forall (_,_)
  | Exists (_,_)
  | Mu _
  | Fun (_,_)
  | Asserting _
  | TyArrow (_,_)
  | TyForall (_,_) -> fpf out "@[(%a)@]" print_term t

and print_typed_var out (v,ty) = match ty with
  | None -> fpf out "%s" v
  | Some ty -> fpf out "(%s:%a)" v print_term ty

let pp_rec_defs out l =
  let ppterms = pp_list_ ~sep:";" print_term in
  let pp_case out (v,ty,l) =
    fpf out "@[<hv2>%s : %a :=@ %a@]" v print_term ty ppterms l in
  fpf out "@[<hv>%a@]" (pp_list_ ~sep:" and " pp_case) l

let pp_spec_defs out (defined_l,l) =
  let ppterms = pp_list_ ~sep:";" print_term in
  let pp_defined out (v,ty) = fpf out "@[%s : %a@]" v print_term ty in
  let pp_defined_list out =
    fpf out "@[<hv>%a@]" (pp_list_ ~sep:" and " pp_defined)
  in
  fpf out "@[<v>%a :=@ %a@]" pp_defined_list defined_l ppterms l

let pp_ty_defs out l =
  let ppcons out (id,args) =
    fpf out "@[%s %a@]" id (pp_list_ ~sep:" " print_term) args in
  let ppcons_l = pp_list_ ~sep:" | " ppcons in
  let pp_case out (id,ty_vars,l) =
    fpf out "@[<hv2>@[<h>%s %a@] :=@ %a@]"
      id (pp_list_ ~sep:" " CCFormat.string) ty_vars ppcons_l l
  in
  fpf out "@[<hv>%a@]" (pp_list_ ~sep:" and " pp_case) l

let pp_wf out = function
  | `Wf -> fpf out "[wf]"
  | `Not_wf -> ()

let pp_mutual_preds out l =
  let pp_def out (p, ty, clauses) =
    fpf out "@[<hv2>@[%s@ : %a@] :=@ %a@]" p print_term ty
      (pp_list_ ~sep:"; " print_term) clauses
  in
  pp_list_ ~sep:" and " pp_def out l

let pp_attr out l = fpf out "@[%a@]" (pp_list_ ~sep:" " CCFormat.string) l
let pp_attrs out = function
  | [] -> ()
  | l -> fpf out "@ [@[%a@]]" (pp_list_ ~sep:"," pp_attr) l

let print_statement out st = match st.stmt_value with
  | Include (f, None) -> fpf out "@[include %s.@]" f
  | Include (f, Some l) -> fpf out "@[include (%a) from %s.@]"
      (pp_list_ ~sep:"," CCFormat.string) l f
  | Decl (v, t, attrs) -> fpf out "@[val %s : %a%a.@]" v print_term t pp_attrs attrs
  | Axiom l -> fpf out "@[axiom @[%a@].@]" (pp_list_ ~sep:";" print_term) l
  | Spec l -> fpf out "@[spec %a.@]" pp_spec_defs l
  | Rec l -> fpf out "@[rec %a.@]" pp_rec_defs l
  | Def (a,b) ->
      fpf out "@[<2>axiom[def]@ %s@ = @[%a@].@]" a print_term b
  | Data l -> fpf out "@[data %a.@]" pp_ty_defs l
  | Codata l -> fpf out "@[codata %a.@]" pp_ty_defs l
  | Goal t -> fpf out "@[goal %a.@]" print_term t
  | Pred (k, preds) -> fpf out "@[pred%a %a.@]" pp_wf k pp_mutual_preds preds
  | Copy c ->
      let pp_pred out = function
        | None -> ()
        | Some p -> fpf out "@ @[pred %a@]" print_term p
      in
      fpf out "@[<v2>@[copy @[%s%a@] :=@ @[%a@]@]@,abstract = %s@,concrete = %s%a@]"
        c.id (pp_list_ ~sep:" " CCFormat.string) c.copy_vars
        print_term c.of_ c.abstract c.concrete pp_pred c.pred
  | Copred (k, preds) -> fpf out "@[copred%a %a.@]" pp_wf k pp_mutual_preds preds

let print_statement_list out l =
  Format.fprintf out "@[<v>%a@]"
    (CCFormat.list ~start:"" ~stop:"" ~sep:"" print_statement) l

module TPTP = struct
  (* additional statements for any TPTP problem *)
  let prelude =
    let (==>) = ty_arrow in
    let ty_term = builtin `Unitype in
    [ decl ~attrs:[] "!!" ((ty_term ==> ty_prop) ==> ty_prop)
    ; decl ~attrs:[] "??" ((ty_term ==> ty_prop) ==> ty_prop)
    ]

  (* meta-data used in TPTP `additional_info` *)
  type general_data =
    | Var of string
    | Int of int
    | String of string
    | App of string * general_data list
    | List of general_data list
    | Column of general_data * general_data
end
