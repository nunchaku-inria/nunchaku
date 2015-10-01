
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Input AST} *)

module Loc = NunLocation
module Sym = NunSymbol

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

type ty = ty_node Loc.with_loc
and ty_node =
  | TySym of Sym.t (** Builtin constant *)
  | TyWildcard
  | TyVar of var
  | TyApp of ty * ty list
  | TyArrow of ty * ty
  | TyForall of var * ty

(** A variable with, possibly, its type *)
type typed_var = var * ty option

type term = term_node Loc.with_loc
and term_node =
  | Sym of Sym.t
  | Var of var
  | App of term * term list
  | Fun of typed_var * term
  | Let of var * term * term
  | Forall of typed_var * term
  | Exists of typed_var * term

type statement_node =
  | Decl of var * ty (* declaration of uninterpreted symbol *)
  | Def of typed_var * term (* definition *)
  | Axiom of term (* axiom *)

type statement = statement_node Loc.with_loc

let ty_sym ?loc s = Loc.with_loc ?loc (TySym s)
let ty_wildcard ?loc () = Loc.with_loc ?loc TyWildcard
let ty_var ?loc v = Loc.with_loc ?loc (TyVar v)
let ty_app ?loc a l = Loc.with_loc ?loc (TyApp (a,l))
let ty_arrow ?loc a b = Loc.with_loc ?loc (TyArrow (a,b))
let ty_forall ?loc v t = Loc.with_loc ?loc (TyForall (v,t))

let sym ?loc s = Loc.with_loc ?loc (Sym s)
let var ?loc v = Loc.with_loc ?loc (Var v)
let app ?loc t l = Loc.with_loc ?loc (App (t,l))
let fun_ ?loc v t = Loc.with_loc ?loc (Fun(v,t))
let fun_l ?loc = List.fold_right (fun_ ?loc)
let let_ ?loc v t u = Loc.with_loc ?loc (Let (v,t,u))
let forall ?loc v t = Loc.with_loc ?loc (Forall (v, t))
let exists ?loc v t = Loc.with_loc ?loc (Exists (v, t))

let forall_list ?loc = List.fold_right (forall ?loc)
let exists_list ?loc = List.fold_right (exists ?loc)

let decl ?loc v t = Loc.with_loc ?loc (Decl(v,t))
let def ?loc v t = Loc.with_loc ?loc (Def (v,t))
let axiom ?loc t = Loc.with_loc ?loc (Axiom t)

(* all elements are distinct? *)
let rec all_diff_ = function
  | [_] | [] -> true
  | x :: tail -> not (List.mem x tail) && all_diff_ tail

(* [def_l v vars t] is [def v (fun vars => t)] *)
let def_l ?loc v vars t =
  if not (all_diff_ (v::vars)) then raise (SyntaxError ("non-linear pattern", loc));
  def ?loc v (fun_l ?loc vars t)

let pf = Format.fprintf

let rec print_ty out ty = match Loc.get ty with
  | TySym s -> Sym.print out s
  | TyWildcard -> CCFormat.string out "_"
  | TyVar v -> CCFormat.string out v
  | TyApp (a, l) ->
      pf out "@[<2>%a@ %a@]"
        print_ty_in_app a
        (CCFormat.list ~start:"" ~stop:"" ~sep:" " print_ty_in_app) l
  | TyArrow (a, b) ->
      pf out "@[<2>%a ->@ %a@]"
        print_ty_in_arrow a print_ty b
  | TyForall (v, t) ->
      pf out "@[<2>pi %s.@ %a@]" v print_ty t
and print_ty_in_app out ty = match Loc.get ty with
  | TyApp _ | TyArrow _ | TyForall _ ->
      pf out "(%a)" print_ty ty
  | TySym _ | TyVar _ | TyWildcard -> print_ty out ty
and print_ty_in_arrow out ty = match Loc.get ty with
  | TyArrow _ | TyForall _ ->
      pf out "(%a)" print_ty ty
  | TyApp _ | TySym _ | TyVar _ | TyWildcard -> print_ty out ty

let print_typed_var out (v,ty) = match ty with
  | None -> pf out "%s" v
  | Some ty -> pf out "%s:%a" v print_ty_in_app ty

let rec print_term out term = match Loc.get term with
  | Sym s -> Sym.print out s
  | Var v -> CCFormat.string out v
  | App (a, l) ->
      pf out "@[<2>%a@ %a@]"
        print_term_inner a
        (CCFormat.list ~start:"" ~stop:"" ~sep:" " print_term_inner) l
  | Fun (v, t) ->
      pf out "@[<2>fun %a =>@ %a@]" print_typed_var v print_term t
  | Let (v,t,u) ->
      pf out "@[<2>let %s :=@ %a in@ %a@]" v print_term t print_term u
  | Forall (v, t) ->
      pf out "@[<2>forall %a.@ %a@]" print_typed_var v print_term t
  | Exists (v, t) ->
      pf out "@[<2>forall %a.@ %a@]" print_typed_var v print_term t
and print_term_inner out term = match Loc.get term with
  | App _ | Fun _ | Let _ | Forall _ | Exists _ ->
      pf out "(%a)" print_term term
  | Sym _ | Var _ -> print_term out term

let print_statement out st = match Loc.get st with
  | Decl (v, t) -> pf out "@[val %s : %a.@]" v print_ty t
  | Def (v, t) -> pf out "@[def %a := %a.@]" print_typed_var v print_term t
  | Axiom t -> pf out "@[axiom %a.@]" print_term t

let print_statement_list out l =
  Format.fprintf out "@[<v>%a@]"
    (CCFormat.list ~start:"" ~stop:"" ~sep:"" print_statement) l
