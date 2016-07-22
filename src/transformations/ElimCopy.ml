
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
type ty = T.t

type decode_state = (term, ty) Env.t

(* encode the copy type as a datatype *)
let copy_as_data ~info (c:_ Stmt.copy): _ Stmt.t list =
  (* the datatype itself, whose cstor is [c.copy_abstract] *)
  let cstor =
    { Stmt.
      cstor_name = c.Stmt.copy_abstract;
      cstor_args = [c.Stmt.copy_of];
      cstor_type = U.ty_arrow c.Stmt.copy_of c.Stmt.copy_to
    }
  in
  let data_ =
    { Stmt.
      ty_id = c.Stmt.copy_id;
      ty_vars = [];
      ty_type = U.ty_type;
      ty_cstors = ID.Map.singleton c.Stmt.copy_abstract cstor
    }
  in
  let decl_data = Stmt.data ~info [data_] in
  (* the definition of [c.copy_concrete], as pattern matching:
     [forall x:concrete. concr (abs x) = x] *)
  let decl_concr =
    let x = Var.make ~ty:c.Stmt.copy_of ~name:"x" in
    let lhs = U.app_const c.Stmt.copy_abstract [U.var x] in
    let rhs = U.var x in
    let def =
      { Stmt.
        rec_defined = Stmt.mk_defined c.Stmt.copy_concrete c.Stmt.copy_concrete_ty;
        rec_vars=[];
        rec_eqns=Stmt.Eqn_nested [[x], [lhs], rhs, []];
      }
    in
    Stmt.axiom_rec ~info:Stmt.info_default [def]
  in
  (* return all new decls *)
  [decl_data; decl_concr]

let elim pb =
  let env = Problem.env pb in
  let pb' =
    Problem.flat_map_statements pb
      ~f:(fun stmt ->
        let info = Stmt.info stmt in
        match Stmt.view stmt with
          | Stmt.Copy c ->
            begin match c.Stmt.copy_pred with
              | None -> copy_as_data ~info c
              | Some _ -> assert false (* TODO: encoding as finite type *)
            end
          | _ -> [stmt]
      )
  in
  pb', env

let decode_model (st:decode_state) m : _ Model.t =
  let env = st in
  Model.filter m
    ~values:(fun (t,_,_) -> match T.repr t with
      | TI.Const id ->
        begin match Env.find ~env id with
          | Some {Env.def=Env.Copy_concrete c; _} ->
            (* drop `concrete` functions *)
            begin match c.Stmt.copy_pred with
              | None -> false
              | Some _ -> assert false (* TODO: set of rewrite rules on constants *)
            end
          | _ -> true
        end
      | _ -> true
    )

let pipe ~print ~check =
  let on_encoded =
    Utils.singleton_if print () ~f:(fun () ->
      let module Ppb = Problem.Print(P)(P) in
      Format.printf "@[<v2>@{<Yellow>after %s@}:@ %a@]@." name Ppb.print)
    @
    Utils.singleton_if check () ~f:(fun () ->
      let module C = TypeCheck.Make(T) in
      C.empty () |> C.check_problem)
  in
  let decode st = Problem.Res.map_m ~f:(decode_model st) in
  Transform.make
    ~name
    ~input_spec:Transform.Features.(of_list [Ty, Mono; Copy, Present])
    ~map_spec:Transform.Features.(update_l [Copy, Absent; Data, Present; Fun, Eqn_nested])
    ~on_encoded
    ~encode:elim
    ~decode
    ()
