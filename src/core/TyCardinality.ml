
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Compute the cardinality of Types} *)

module TI = TermInner
module Stmt = Statement

exception Error of string

exception Polymorphic

let error_ msg = raise (Error msg)
let errorf_ msg = CCFormat.ksprintf msg ~f:error_

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
    | Unknown, _
    | _, Unknown -> Unknown  (* absorbs everything *)
    | Bounded x, _
    | _, Bounded x when Z.sign x = 0 -> zero  (* absorption by 0 *)
    | Bounded a, Bounded b -> Bounded Z.(a*b)
    | _ -> Infinite

  let one = Bounded Z.one
  let of_int i = Bounded (Z.of_int i)
  let of_z i = Bounded i
  let unknown = Unknown
  let infinite = Infinite

  let equal a b = match a, b with
    | Bounded a, Bounded b -> Z.equal a b
    | Unknown, _
    | _, Unknown -> false (* heh. *)
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

module Make(T : TI.S) = struct
  module U = TI.UtilRepr(T)
  module P = TI.Print(T)

  type ty = T.t
  type ('a, 'inv) env = ('a, ty, 'inv) Env.t constraint 'inv = <ty:[`Mono]; ..>

  let is_nullary_cstor_ c = c.Stmt.cstor_args = []

  (* [l] is a well-founded mutual data definition if some of its
     type has at least one nullary constructor *)
  let is_wf_data_ l =
    List.exists
      (fun d -> ID.Map.exists (fun _ -> is_nullary_cstor_) d.Stmt.ty_cstors)
      l

  type _ op_ =
    | Op_card_id : ID.t op_
    | Op_card_ty : ty op_

  let cardinality_ (type a) (op : a op_) env (arg : a) =
    (* recurse through sub-definitions.
       @param map of already computed types, for avoiding loops *)
    let rec aux m id =
      match ID.Map.get id m with
      | Some c -> c
      | None ->
          let info = Env.find_exn ~env id in
          if not (U.ty_is_Type info.Env.ty)
            then raise Polymorphic; (* only monomorphic! *)
          match Env.def info with
            | Env.Data (`Data,l,_) when not (is_wf_data_ l) ->
                Card.zero (* not well founded *)
            | Env.Data (`Data,_,def) ->
                (* - add [id -> infinite] to [m]
                   - compute sum of cardinalities of constructors,
                     i.e. the product of cardinalities of arguments with new [m] *)
                let m = ID.Map.add id Card.infinite m in
                ID.Map.fold
                  (fun _c_id c acc ->
                    let n_c =
                      List.fold_left
                        (fun n arg -> let n_arg = aux_ty m arg in Card.( n * n_arg))
                        Card.one c.Stmt.cstor_args
                    in
                    Card.(n_c + acc))
                  def.Stmt.ty_cstors
                  Card.zero
            | Env.Data (`Codata,_,_) ->
                (* TODO: uhhh? :s
                   we should do like the Data case, except that the fixpoint
                   is not trivial. For instance, for the type
                   [stream := Cons t stream], we have:
                     - if [card t = 0], then [card stream = 0]
                     - if [card t = 1], then [card stream = 1]
                     - else [card stream = infinite]
                     *)
                Utils.not_implemented "cardinality of codata"
            | Env.Copy_ty c ->
                begin match c.Stmt.copy_pred with
                | Some _ -> Card.unknown (* restriction of size? *)
                | None -> aux_ty m c.Stmt.copy_of (* cardinality of definition *)
                end
            | Env.NoDef -> Card.unknown
            | Env.Cstor _
            | Env.Fun_def (_,_,_)
            | Env.Fun_spec (_,_)
            | Env.Pred (_,_,_,_,_)
            | Env.Copy_abstract _
            | Env.Copy_concretize _ -> errorf_ "%a is not a type" ID.print id
    (* compute the cardinality of a type *)
    and aux_ty m ty = match T.repr ty with
      | TI.Const id -> aux m id
      | TI.App (f, _) -> aux_ty m f
      | _ -> errorf_ "cannot compute cardinality of type@ `@[%a@]`" P.print ty
    in
    match op with
    | Op_card_id -> aux ID.Map.empty arg
    | Op_card_ty -> aux_ty ID.Map.empty arg

  let cardinality_ty_id env id = cardinality_ Op_card_id env id
  let cardinality_ty env ty = cardinality_ Op_card_ty env ty
end
