
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Compute the cardinality of Types} *)

module TI = TermInner
module Stmt = Statement

exception Error of string

exception Polymorphic

let error_ msg = raise (Error msg)
let errorf_ msg = CCFormat.ksprintf msg ~f:error_

let fpf = Format.fprintf
let section = Utils.Section.make "ty_cardinality"

let () = Printexc.register_printer
  (function
    | Error msg -> Some (Utils.err_sprintf "ty cardinality: %s" msg)
    | Polymorphic -> Some (Utils.err_sprintf "type is polymorphic")
    | _ -> None)

(** Approximation of a cardinal, including infinite cardinals *)
module Card = struct
  type t =
    | Bounded of Z.t
    | Unknown
    | Infinite

  let (+) a b = match a, b with
    | Unknown, (Unknown | Bounded _)
    | Bounded _, Unknown -> Unknown
    | Bounded a, Bounded b -> Bounded Z.(a+b)
    | Infinite, _
    | _, Infinite -> Infinite (* even infinite+unknown = infinite *)

  let zero = Bounded Z.zero

  let ( * ) a b = match a, b with
    | Bounded x, _
    | _, Bounded x when Z.sign x = 0 -> zero (* absorption by 0 *)
    | Infinite, _
    | _, Infinite ->
        (* XXX we assume uninterpreted types are not empty, therefore
           ∞ × unknown = ∞ *)
        Infinite
    | Bounded a, Bounded b -> Bounded Z.(a*b)
    | Unknown, _
    | _, Unknown -> Unknown  (* absorbs bounded *)

  let one = Bounded Z.one
  let of_int i = Bounded (Z.of_int i)
  let of_z i = Bounded i
  let unknown = Unknown
  let infinite = Infinite
  let is_zero = function Bounded z -> Z.sign z = 0 | _ -> false

  let equal a b = match a, b with
    | Bounded a, Bounded b -> Z.equal a b
    | Unknown, _
    | _, Unknown -> true (* heh. *)
    | Infinite, Infinite -> true
    | Infinite, Bounded _
    | Bounded _, Infinite -> false

  let hash = function
    | Bounded x -> Z.hash x
    | Unknown -> 13
    | Infinite -> 17
  let hash_fun x = CCHash.int (hash x)

  let print out = function
    | Bounded x -> Z.pp_print out x
    | Unknown -> CCFormat.string out "<unknown>"
    | Infinite -> CCFormat.string out "ω"
end

(** Symbolic expressions *)
module Expr = struct
  type t =
    | Const of Card.t
    | Var of ID.t
    | Plus of t * t
    | Mult of t * t

  (* evaluate an expression *)
  let rec eval subst = function
    | Const n -> n
    | Var id -> ID.Map.find id subst
    | Plus (a,b) -> Card.(eval subst a + eval subst b)
    | Mult (a,b) -> Card.(eval subst a * eval subst b)

  let unknown = Const Card.unknown
  let infinite = Const Card.infinite
  let const n = Const n
  let zero = const Card.zero
  let one = const Card.one
  let var id = Var id

  let ( + ) a b = match a, b with
    | Const a, Const b -> const Card.(a + b)
    | Const Card.Infinite, _
    | _, Const Card.Infinite -> const Card.infinite
    | (Const z, e | e, Const z) when Card.is_zero z -> e
    | _ -> Plus (a,b)

  let ( * ) a b = match a, b with
    | Const a, Const b -> const Card.(a * b)
    | (Const z, _ | _, Const z) when Card.is_zero z -> const Card.zero
    | (Const (Card.Bounded x), e
    | e, Const (Card.Bounded x)) when Z.equal x Z.one -> e
    | Const Card.Infinite, _
    | _, Const Card.Infinite ->
        (* XXX: here we favor infinite over unknown, meaning there
           is no empty uninterpreted type (i.e. unknown still > 0) *)
        const Card.infinite
    | _ -> Mult (a,b)

  let rec print out = function
    | Const c -> Card.print out c
    | Var v -> ID.print out v
    | Plus (a,b) -> fpf out "@[%a +@ %a@]" print_in a print_in b
    | Mult (a,b) -> fpf out "@[%a *@ %a@]" print a print b
  and print_in out = function
    | Plus _ as e -> fpf out "(@[%a@])" print e
    | e -> print out e
end

module Make(T : TI.S) = struct
  module U = TI.UtilRepr(T)
  module P = TI.Print(T)

  type ty = T.t
  type ('a, 'inv) env = ('a, ty, 'inv) Env.t constraint 'inv = <ty:[`Mono]; ..>

  (* cache: maps IDs to (fully computed) cardinalities *)
  type cache = Card.t ID.Tbl.t

  let create_cache () = ID.Tbl.create 16

  let is_nullary_cstor_ c = c.Stmt.cstor_args = []

  (* [d] is a well-founded data definition if it has a nullary constructor,
     that is, a base case *)
  let is_wf_data_ d =
      ID.Map.exists (fun _ -> is_nullary_cstor_) d.Stmt.ty_cstors

  (* system of equations:
     map from [id] (a type symbol) to:
       - an expr [e] such that [cardinal id = e]
       - an approximation of the cardinal of [id] used for self-recursion
  *)
  type equations = {
    rhs: Expr.t ID.Map.t; (* subset of cur, holds RHS of equations *)
    cur: Card.t ID.Map.t; (* current value, used in fixpoint *)
  }

  let pp_equations out m =
    let pp_lhs out id = fpf out "@[%a " ID.print id in
    let pp_rhs out e = fpf out "@[%a@]@]" Expr.print e in
    fpf out "@[<v>%a@]"
      (ID.Map.print ~start:"" ~stop:"" ~sep:"" ~arrow:" = " pp_lhs pp_rhs) m.rhs

  (* find the system of equations for the type's cardinality *)
  let rec card_of_ty_id_ cache env eqns id : Expr.t =
    match ID.Tbl.get cache id with
    | Some c -> Expr.const c (* I know that! *)
    | None when ID.Map.mem id (!eqns).rhs ->
        (* we have an equation for [id], so just use a variable *)
        Expr.var id
    | None ->
        let info = Env.find_exn ~env id in
        if not (U.ty_is_Type info.Env.ty)
          then raise Polymorphic; (* only monomorphic! *)
        match Env.def info with
          | Env.Data _ when ID.Map.mem id (!eqns).cur ->
              (* currently in a fixpoint *)
              Expr.var id
          | Env.Data (d,_,def) ->
              (* there is no approximation of [card id] yet, add one *)
              let approx =
                if is_wf_data_ def then Card.infinite
                else match d with
                  | `Data -> Card.zero
                  | `Codata -> Card.one (* at least one infinite chain *)
              in
              (* add to [eqns.cur] before computing RHS of equations, for
                 termination purpose *)
              eqns := { !eqns with cur = ID.Map.add id approx (!eqns).cur; };
              (* now compute the equation *)
              let eqn = ID.Map.fold
                (fun _c_id c acc ->
                  let n_c =
                    List.fold_left
                      (fun n arg ->
                        let n_arg = card_of_ty_ cache env eqns arg in
                        Expr.( n * n_arg))
                      Expr.one c.Stmt.cstor_args
                  in
                  Expr.(n_c + acc))
                def.Stmt.ty_cstors
                Expr.zero
              in
              eqns := {!eqns with rhs = ID.Map.add id eqn (!eqns).rhs; };
              (* still, return a variable *)
              Expr.var id
          | Env.Copy_ty c ->
              begin match c.Stmt.copy_pred with
              | Some _ -> Expr.unknown (* restriction of size? *)
              | None -> card_of_ty_ cache env eqns c.Stmt.copy_of (* cardinality of definition *)
              end
          | Env.NoDef -> Expr.unknown
          | Env.Cstor _
          | Env.Fun_def (_,_,_)
          | Env.Fun_spec (_,_)
          | Env.Pred (_,_,_,_,_)
          | Env.Copy_abstract _
          | Env.Copy_concretize _ -> errorf_ "%a is not a type" ID.print id
  (* compute the cardinality of a type *)
  and card_of_ty_ cache env eqns ty = match T.repr ty with
    | TI.Const id -> card_of_ty_id_ cache env eqns id
    | TI.App (f, _) -> card_of_ty_ cache env eqns f
    | _ -> errorf_ "cannot compute cardinality of type@ `@[%a@]`" P.print ty

  (* compute fixpoint of [eqns] and returns a map [lhs --> card] *)
  let fixpoint_ eqns =
    Utils.debugf ~section 5 "@[<2>fix@ equations %a@]@."
      (fun k->k pp_equations eqns);
    let rec aux m =
      let m' =
        ID.Map.map
          (fun rhs -> Expr.eval m rhs)
          eqns.rhs
      in
      Utils.debugf ~section 5 "@[<2>values @[%a@]@]@."
        (fun k->k (ID.Map.print ID.print Card.print) m');
      if ID.Map.equal Card.equal m m' then m (* reached fixpoint *)
      else aux m'
    in
    Utils.debugf ~section 5 "@[<2>values @[%a@]@]@."
      (fun k->k (ID.Map.print ID.print Card.print) eqns.cur);
    aux eqns.cur

  let solve_ cache eqns =
    Utils.debugf ~section 4 "@[<2>equations:@ @[%a@]@]"
      (fun k->k pp_equations eqns);
    let subst = fixpoint_ eqns in
    (* add to cache *)
    subst |> ID.Map.to_seq |> ID.Tbl.add_seq cache;
    subst

  let cardinality_ty_id ?(cache=create_cache ()) env id =
    let eqns = ref {cur=ID.Map.empty; rhs=ID.Map.empty; } in
    let expr = card_of_ty_id_ cache env eqns id in
    let subst = solve_ cache !eqns in
    Expr.eval subst expr

  let cardinality_ty ?(cache=create_cache()) env ty =
    let eqns = ref {cur=ID.Map.empty; rhs=ID.Map.empty; } in
    let expr = card_of_ty_ cache env eqns ty in
    let subst = solve_ cache !eqns in
    Expr.eval subst expr
end
