
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Eliminate "if/then/else"} *)

open Nunchaku

module T = FO.T

type term = FO.T.t
type ty = FO.Ty.t
type problem = (term, ty) FO.Problem.t

let name = "elim_ite"
let section = Utils.Section.make name

module TSet = CCSet.Make(T)

(* conjunction of propositional terms that contain no "ite" *)
type cond = TSet.t

(* conjunction of the elements in the set *)
let and_set_ s =
  s |> TSet.remove T.true_ |> TSet.elements |> T.and_

module Ite_M = struct
  (* a decision tree that can be moved "outside" the terms by using a monad *)
  type +'a t =
    | Yield of 'a
    | Ite of cond * 'a t * 'a t

  let return x = Yield x

  (* add a test; if the test holds yield [b], else yield [c] *)
  let ite
    : cond -> 'a t -> 'a t -> 'a t
    = fun a b c -> Ite (a, b, c)

  let rec (>|=)
    : 'a t -> ('a -> 'b) -> 'b t
    = fun x f -> match x with
      | Yield x -> return (f x)
      | Ite (cond,a,b) -> ite cond (a >|= f) (b >|= f)

  let rec (>>=)
    : 'a t -> ('a -> 'b t) -> 'b t
    = fun x f -> match x with
      | Yield y -> f y
      | Ite (cond, a, b) ->
        ite cond (a >>= f) (b >>= f)

  let (<*>)
    : ('a -> 'b) t -> 'a t -> 'b t
    = fun f x ->
      f >>= fun f ->
      x >|= fun x -> f x

  let rec fold_m f acc l = match l with
    | [] -> return acc
    | [x] -> f acc x
    | x :: tail ->
      f acc x >>= fun acc -> fold_m f acc tail
end

let transform_term t =
  let open Ite_M in
  let rec aux subst t : term Ite_M.t = match T.view t with
    | FO.Builtin _
    | FO.DataTest (_,_)
    | FO.DataSelect (_,_,_)
    | FO.Undefined (_,_)
    | FO.Undefined_atom _
    | FO.Unparsable _
    | FO.Mu (_,_)
    | FO.True
    | FO.False -> return t
    | FO.Var v ->
      return (CCOpt.get_or ~default:t (Var.Subst.find ~subst v))
    | FO.Eq (a,b) -> return T.eq <*> aux subst a <*> aux subst b
    | FO.Equiv (a,b) -> return T.equiv <*> aux subst a <*> aux subst b
    | FO.Imply (a,b) -> return T.imply <*> aux subst a <*> aux subst b
    | FO.Ite (a,b,c) ->
      aux subst a >>= fun a ->
      ite (TSet.singleton a)
        (aux subst b)
        (aux subst c)
    | FO.And l -> aux_l subst l >|= T.and_
    | FO.Or l -> aux_l subst l >|= T.or_
    | FO.Not t -> aux subst t >|= T.not_
    | FO.App (id,l) -> aux_l subst l >|= T.app id
    | FO.Let (v,t,u) ->
      (* expand `let` on the fly *)
      aux subst t >>= fun t ->
      let subst' = Var.Subst.add ~subst v t in
      aux subst' u
    | FO.Fun _ -> assert false (* TODO: doomed, if guards contain the bound var *)
    | FO.Forall (v,body) ->
      (* flatten here, otherwise the guards might contain [v] *)
      return (T.forall v (aux_top subst body))
    | FO.Exists (v,body) ->
      return (T.exists v (aux_top subst body))
  and aux_l subst l =
    fold_m
      (fun l x -> aux subst x >|= fun y -> y :: l)
      [] l
    >|= List.rev
  (* transform a toplevel property *)
  and aux_top subst t =
    aux subst t |> ite_to_term
  and ite_to_term t = match t with
    | Yield x -> x
    | Ite (conds,a,b) ->
      let conds = and_set_ conds in
      T.and_
        [ T.imply conds (ite_to_term a);
          T.imply (T.not_ conds) (ite_to_term b);
        ]
  in
  let res = aux_top Var.Subst.empty t in
  Utils.debugf ~section 5 "@[<2>encoded `@[%a@]`@ into `@[%a@]@]"
    (fun k->k FO.print_term t FO.print_term res);
  res

let transform_statement st =
  Utils.debugf ~section 3 "@[<2>transform @{<cyan>statement@}@ `@[%a@]`@]"
    (fun k->k FO.print_statement st);
  match st with
  | FO.TyDecl _
  | FO.Decl _
  | FO.CardBound _
  | FO.MutualTypes _ -> st
  | FO.Axiom f -> FO.Axiom (transform_term f)
  | FO.Goal f -> FO.Goal (transform_term f)

let transform_problem pb =
  let meta = FO.Problem.meta pb in
  FO.Problem.map ~meta transform_statement pb

let pipe ~print =
  let on_encoded =
    Utils.singleton_if print () ~f:(fun () ->
      Format.printf "@[<2>@{<Yellow>after elim_ite@}: {@,@[%a@]@,}@]@."
        FO.print_problem)
  in
  Transform.make
    ~name
    ~on_encoded
    ~input_spec:Transform.Features.(of_list [Fun, Absent])
    ~map_spec:Transform.Features.(update If_then_else Absent)
    ~encode:(fun pb -> transform_problem pb, ())
    ~decode:(fun () m -> m)
    ()
