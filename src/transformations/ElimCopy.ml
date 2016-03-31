
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Eliminate Copy Types} *)

open Nunchaku_core

module TI = TermInner
module Stmt = Statement

type ('a,'b) inv = <eqn:'a; ind_preds:'b; ty:[`Mono]>

let name = "elim_copy"

module Make(T : TI.S) = struct
  module U = TI.Util(T)
  module P = TI.Print(T)

  type term = T.t

  (* id function of type [ty -> ty] *)
  let id_ ty =
    let v = Var.make ~name:"x" ~ty in
    U.fun_ v (U.var v)

  let as_copy_ ~env id =
    let info = Env.find_exn ~env id in
    match Env.def info with
    | Env.Copy_abstract c -> `Abs c
    | Env.Copy_concrete c -> `Conc c
    | Env.Copy_ty c -> `Ty c
    | _ -> `Not_copy

  (* recursively rewrite the term, doing:
    - rewrite terms by removing abstract/concretization functions
    - change type to its definition, including in variables and other types
      (should be just a constant since we are after monomorphization)
    - TODO insert `asserting pred` if the predicate is not None
    *)
  let rec rewrite_term ~env subst t = match T.repr t with
    | TI.Var v ->
        begin match Var.Subst.find ~subst v with
        | None -> t
        | Some v' -> U.var v'
        end
    | TI.Const id ->
        begin match as_copy_ ~env id with
        | `Not_copy -> t
        | `Abs c
        | `Conc c -> id_ c.Stmt.copy_of (* identity *)
        | `Ty c -> c.Stmt.copy_of
        end
    | TI.App (f, l) ->
        let l = List.map (rewrite_term ~env subst) l in
        begin match T.repr f with
        | TI.Const id ->
            begin match as_copy_ ~env id, l with
            | _, [] -> assert false
            | (`Abs _ | `Conc _), f :: l -> U.app f l (* erase *)
            | `Ty _, _ -> assert false
            | `Not_copy, _ -> rewrite_rec_ ~env subst t
            end
        | _ -> rewrite_rec_ ~env subst t
        end
    | _ -> rewrite_rec_ ~env subst t
  and rewrite_rec_ ~env subst t =
    U.map subst t
      ~bind:(fun subst v ->
        (* maybe the type of [v] contains occurrences of copy types *)
        let ty = Var.ty v in
        let ty = rewrite_term ~env subst ty in
        let v' = Var.make ~name:(Var.name v) ~ty in
        Var.Subst.add ~subst v v', v')
      ~f:(rewrite_term ~env)

  let elim pb =
    let env = Problem.env pb in
    Problem.flat_map_statements pb
    ~f:(fun st ->
      match Stmt.view st with
      | Stmt.Copy _ -> [] (* remove *)
      |_ ->
          let f = rewrite_term ~env Var.Subst.empty in
          [Stmt.map ~term:f ~ty:f st])

  let pipe ~print ~check =
    let on_encoded =
      Utils.singleton_if print () ~f:(fun () ->
        let module Ppb = Problem.Print(P)(P) in
        Format.printf "@[<v2>@{<Yellow>after elimination of copy types@}:@ %a@]@." Ppb.print)
      @
      Utils.singleton_if check () ~f:(fun () ->
        let module C = TypeCheck.Make(T) in
        C.check_problem ?env:None)
    in
    Transform.make1
      ~name
      ~on_encoded
      ~encode:(fun pb -> elim pb, ())
      ~decode:(fun () x -> x)
      ()
end
