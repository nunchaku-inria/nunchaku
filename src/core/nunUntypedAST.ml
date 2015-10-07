
(* This file is free software, part of nunchaku. See file "license" for more details. *)

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

module Builtin : sig
  type t =
    | Prop
    | Type
    | Not
    | And
    | Or
    | True
    | False
    | Eq
    | Imply
    | Equiv

  include NunIntf.PRINT with type t := t
  val fixity : t -> [`Prefix | `Infix]
  val to_string : t -> string
end = struct
type t =
  | Prop
  | Type
  | Not
  | And
  | Or
  | True
  | False
  | Eq
  | Imply
  | Equiv

  let fixity = function
    | Type
    | True
    | False
    | Prop
    | Not -> `Prefix
    | And
    | Or
    | Imply
    | Eq
    | Equiv -> `Infix

  let to_string = function
    | Type -> "type"
    | Prop -> "prop"
    | Not -> "~"
    | And -> "&"
    | Or -> "|"
    | True -> "true"
    | False -> "false"
    | Eq -> "="
    | Imply -> "==>"
    | Equiv -> "<=>"

  let print out s = Format.pp_print_string out (to_string s)
end


type term = term_node Loc.with_loc
and term_node =
  | Wildcard
  | Builtin of Builtin.t
  | Var of var
  | AtVar of var  (* variable without implicit arguments *)
  | App of term * term list
  | Fun of typed_var * term
  | Let of var * term * term
  | Ite of term * term * term
  | Forall of typed_var * term
  | Exists of typed_var * term
  | TyArrow of ty * ty
  | TyForall of var * ty

(* we mix terms and types because it is hard to know, in
  [@cons a b c], which ones of [a, b, c] are types, and which ones
  are terms *)
and ty = term

(** A variable with, possibly, its type *)
and typed_var = var * ty option

type statement_node =
  | Decl of var * ty (* declaration of uninterpreted symbol *)
  | Def of typed_var * term (* definition *)
  | Axiom of term (* axiom *)
  | Goal of term (* goal *)

type statement = statement_node Loc.with_loc

let wildcard ?loc () = Loc.with_loc ?loc Wildcard
let builtin ?loc s = Loc.with_loc ?loc (Builtin s)
let var ?loc v = Loc.with_loc ?loc (Var v)
let at_var ?loc v = Loc.with_loc ?loc (AtVar v)
let app ?loc t l = Loc.with_loc ?loc (App (t,l))
let fun_ ?loc v t = Loc.with_loc ?loc (Fun(v,t))
let fun_l ?loc = List.fold_right (fun_ ?loc)
let let_ ?loc v t u = Loc.with_loc ?loc (Let (v,t,u))
let ite ?loc a b c = Loc.with_loc ?loc (Ite (a,b,c))
let forall ?loc v t = Loc.with_loc ?loc (Forall (v, t))
let exists ?loc v t = Loc.with_loc ?loc (Exists (v, t))
let ty_arrow ?loc a b = Loc.with_loc ?loc (TyArrow (a,b))
let ty_forall ?loc v t = Loc.with_loc ?loc (TyForall (v,t))

let ty_forall_list ?loc = List.fold_right (ty_forall ?loc)

let forall_list ?loc = List.fold_right (forall ?loc)
let exists_list ?loc = List.fold_right (exists ?loc)

let decl ?loc v t = Loc.with_loc ?loc (Decl(v,t))
let def ?loc v t = Loc.with_loc ?loc (Def (v,t))
let axiom ?loc t = Loc.with_loc ?loc (Axiom t)
let goal ?loc t = Loc.with_loc ?loc (Goal t)

(* all elements are distinct? *)
let rec all_diff_ = function
  | [_] | [] -> true
  | x :: tail -> not (List.mem x tail) && all_diff_ tail

(* [def_l v vars t] is [def v (fun vars => t)] *)
let def_l ?loc v vars t =
  if not (all_diff_ (v::vars)) then raise (SyntaxError ("non-linear pattern", loc));
  def ?loc v (fun_l ?loc vars t)

let pf = Format.fprintf

let rec print_term out term = match Loc.get term with
  | Wildcard -> CCFormat.string out "_"
  | Builtin s -> Builtin.print out s
  | Var v -> CCFormat.string out v
  | AtVar v -> pf out "@%s" v
  | App (f, [a;b]) ->
      begin match Loc.get f with
      | Builtin s when Builtin.fixity s = `Infix ->
          pf out "@[<2>%a@ %a@ %a@]"
            print_term_inner a Builtin.print s print_term_inner b
      | _ ->
          pf out "@[<2>%a@ %a@ %a@]" print_term_inner f
            print_term_inner a print_term_inner b
      end
  | App (a, l) ->
      pf out "@[<2>%a@ %a@]"
        print_term_inner a
        (CCFormat.list ~start:"" ~stop:"" ~sep:" " print_term_inner) l
  | Fun (v, t) ->
      pf out "@[<2>fun %a.@ %a@]" print_typed_var v print_term t
  | Let (v,t,u) ->
      pf out "@[<2>let %s :=@ %a in@ %a@]" v print_term t print_term u
  | Ite (a,b,c) ->
      pf out "@[<2>if %a@ then %a@ else %a@]"
        print_term a print_term b print_term c
  | Forall (v, t) ->
      pf out "@[<2>forall %a.@ %a@]" print_typed_var v print_term t
  | Exists (v, t) ->
      pf out "@[<2>forall %a.@ %a@]" print_typed_var v print_term t
  | TyArrow (a, b) ->
      pf out "@[<2>%a ->@ %a@]"
        print_term_in_arrow a print_term b
  | TyForall (v, t) ->
      pf out "@[<2>forall (%s:type).@ %a@]" v print_term t
and print_term_inner out term = match Loc.get term with
  | App _ | Fun _ | Let _ | Ite _
  | Forall _ | Exists _ | TyForall _ | TyArrow _ ->
      pf out "(%a)" print_term term
  | Builtin _ | AtVar _ | Var _ | Wildcard -> print_term out term
and print_term_in_arrow out t = match Loc.get t with
  | Wildcard
  | Builtin _
  | Var _
  | AtVar _
  | App (_,_) -> print_term out t
  | Let (_,_,_)
  | Ite _
  | Forall (_,_)
  | Exists (_,_)
  | Fun (_,_)
  | TyArrow (_,_)
  | TyForall (_,_) -> pf out "@[(%a)@]" print_term t

and print_typed_var out (v,ty) = match ty with
  | None -> pf out "%s" v
  | Some ty -> pf out "(%s:%a)" v print_term ty

let print_statement out st = match Loc.get st with
  | Decl (v, t) -> pf out "@[val %s : %a.@]" v print_term t
  | Def (v, t) -> pf out "@[def %a := %a.@]" print_typed_var v print_term t
  | Axiom t -> pf out "@[axiom %a.@]" print_term t
  | Goal t -> pf out "@[goal %a.@]" print_term t

let print_statement_list out l =
  Format.fprintf out "@[<v>%a@]"
    (CCFormat.list ~start:"" ~stop:"" ~sep:"" print_statement) l
