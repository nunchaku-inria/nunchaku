
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Eliminate "if/then/else"} *)

open Nunchaku_core

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
  (* returns a sequence of (conditions, 'a).
     Invariant: The last case is the only one to have an empty list of conditions *)
  type +'a t = (cond * 'a) Sequence.t

  let return x = Sequence.return (TSet.empty, x)

  let (>|=)
    : 'a t -> ('a -> 'b) -> 'b t
    = fun x f ->
      let open Sequence.Infix in
      x >|= fun (conds, t) -> conds, f t

  let (<*>)
    : ('a -> 'b) t -> 'a t -> 'b t
    = fun f x ->
      let open Sequence.Infix in
      f >>= fun (conds_f,f') ->
      x >|= fun (conds_x,x') ->
      TSet.union conds_f conds_x, f' x'

  let (>>=)
    : 'a t -> ('a -> 'b t) -> 'b t
    = fun x f ->
      let open Sequence.Infix in
      x >>= fun (conds, t) ->
      f t >|= fun (conds', t') -> TSet.union conds' conds, t'

  (* add a test; if the test holds yield [b], else yield [c] *)
  let guard
    : cond -> 'a t -> 'a t -> 'a t
    = fun a b c ->
      Sequence.append
        (Sequence.map (fun (a',b') -> TSet.union a a', b') b)
        c

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
      return (CCOpt.get t (Var.Subst.find ~subst v))
    | FO.Eq (a,b) -> return T.eq <*> aux subst a <*> aux subst b
    | FO.Equiv (a,b) -> return T.equiv <*> aux subst a <*> aux subst b
    | FO.Imply (a,b) -> return T.imply <*> aux subst a <*> aux subst b
    | FO.Ite (a,b,c) ->
      aux subst a >>= fun a ->
      guard (TSet.singleton a)
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
    aux subst t
    |> Sequence.to_list
    |> CCList.fold_map
      (fun prev_conds (cond,t) ->
         (* if there are some previous conditions, require their negation
            so the current case is orthogonal to the previous cases *)
         let prev_conds' = TSet.diff prev_conds cond |> TSet.remove T.true_ in
         let cond' =
           if TSet.is_empty prev_conds'
           then cond
           else (* cond && not (prev_conds \ cond) *)
             TSet.add (T.not_ (and_set_ prev_conds')) cond
         in
         let t' = T.imply (and_set_ cond') t in
         TSet.union cond prev_conds, t')
      TSet.empty
    |> snd (* drop the list of conditions *)
    |> T.and_
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
