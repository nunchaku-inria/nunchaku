
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Eliminate Copy Types} *)

open Nunchaku_core

module TI = TermInner
module Stmt = Statement
module T = TermInner.Default
module U = T.U
module P = T.P

let name = "elim_copy"

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
  U.map subst t ~bind:(bind_var ~env) ~f:(rewrite_term ~env)

and bind_var ~env subst v =
  (* maybe the type of [v] contains occurrences of copy types *)
  let ty = Var.ty v in
  let ty = rewrite_term ~env subst ty in
  let v' = Var.make ~name:(Var.name v) ~ty in
  Var.Subst.add ~subst v v', v'

let elim pb =
  Problem.check_features pb
    ~spec:Problem.Features.(of_list [Ty, Mono]);
  let env = Problem.env pb in
  Problem.flat_map_statements pb
  ~f:(fun st ->
    match Stmt.view st with
    | Stmt.Copy _ -> [] (* remove *)
    |_ ->
        let f = rewrite_term ~env in
        [Stmt.map_bind Var.Subst.empty st ~bind:(bind_var ~env) ~term:f ~ty:f ])

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
  Transform.make
    ~name
    ~on_encoded
    ~encode:(fun pb -> elim pb, ())
    ~decode:(fun () x -> x)
    ()
