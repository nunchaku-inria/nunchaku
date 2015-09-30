
(* This file is free software, part of containers. See file "license" for more details. *)

(** {1 Input AST} *)

module Loc = NunLocation

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
  | TyVar of var
  | TyApp of ty * ty list
  | TyArrow of ty * ty

type term = term_node Loc.with_loc
and term_node =
  | Var of var
  | App of term * term list
  | Fun of var * term

type statement_node =
  | Decl of var * ty (* type declaration *)
  | Def of var * term (* definition *)
  | Axiom of term (* axiom *)

type statement = statement_node Loc.with_loc

let ty_var ?loc v = Loc.with_loc ?loc (TyVar v)
let ty_app ?loc a l = Loc.with_loc ?loc (TyApp (a,l))
let ty_arrow ?loc a b = Loc.with_loc ?loc (TyArrow (a,b))

let var ?loc v = Loc.with_loc ?loc (Var v)

let app ?loc t l = Loc.with_loc ?loc (App (t,l))
let fun_ ?loc v t = Loc.with_loc ?loc (Fun(v,t))
let fun_l ?loc vars t = List.fold_right (fun v t -> fun_ ?loc v t) vars t

let decl ?loc v t = Loc.with_loc ?loc (Decl(v,t))
let def ?loc v t = Loc.with_loc ?loc (Def (v,t))

(* all elements are distinct? *)
let rec all_diff_ = function
  | [_] | [] -> true
  | x :: tail -> not (List.mem x tail) && all_diff_ tail

(* [def_l v vars t] is [def v (fun vars => t)] *)
let def_l ?loc v vars t =
  if not (all_diff_ (v::vars)) then raise (SyntaxError ("non-linear pattern", loc));
  def ?loc v (fun_l ?loc vars t)

let axiom ?loc t = Loc.with_loc ?loc (Axiom t)

let pf = Format.fprintf

let rec print_ty out ty = match Loc.get ty with
  | TyVar v -> CCFormat.string out v
  | TyApp (a, l) ->
      pf out "@[<2>%a@ %a@]"
        print_ty_in_app a
        (CCFormat.list ~start:"" ~stop:"" ~sep:" " print_ty_in_app) l
  | TyArrow (a, b) ->
      pf out "@[<2>%a ->@ %a@]"
        print_ty_in_fun a print_ty b
and print_ty_in_app out ty = match Loc.get ty with
  | TyApp _ | TyArrow _ ->
      pf out "(%a)" print_ty ty
  | TyVar _ -> print_ty out ty
and print_ty_in_fun out ty = match Loc.get ty with
  | TyArrow _ ->
      pf out "(%a)" print_ty ty
  | TyApp _ | TyVar _ -> print_ty out ty


let rec print_term out term = match Loc.get term with
  | Var v -> CCFormat.string out v
  | App (a, l) ->
      pf out "@[<2>%a@ %a@]"
        print_term_inner a
        (CCFormat.list ~start:"" ~stop:"" ~sep:" " print_term_inner) l
  | Fun (v, t) ->
      pf out "@[<2>fun %s =>@ %a@]" v print_term t
and print_term_inner out term = match Loc.get term with
  | App _ | Fun _ ->
      pf out "(%a)" print_term term
  | Var _ -> print_term out term

let print_statement out st = match Loc.get st with
  | Decl (v, t) -> pf out "@[val %s : %a.@]" v print_ty t
  | Def (v, t) -> pf out "@[def %s := %a.@]" v print_term t
  | Axiom t -> pf out "@[axiom %a.@]" print_term t

let print_statement_list out l =
  Format.fprintf out "@[<v>%a@]"
    (CCFormat.list ~start:"" ~stop:"" ~sep:"" print_statement) l

