
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Eliminate Inductive Predicates} *)

module TI = TermInner
module Stmt = Statement

type 'a inv1 = <eqn:'a; ty:[`Mono]; ind_preds:[`Present]>
type 'a inv2 = <eqn:'a; ty:[`Mono]; ind_preds:[`Absent]>

module Make(T : TI.S) = struct
  module P = TI.Print(T)

  type term = T.t
  type decode_state = unit

  let elim_ind_preds
  : (term, term, 'a inv1) Problem.t ->
    (term, term, 'a inv2) Problem.t * decode_state
  = fun pb ->
    let pb' = Problem.map_statements pb
      ~f:(fun st ->
          let info = Stmt.info st in
          match Stmt.view st with
          | Stmt.Pred _ -> assert false
          | Stmt.Decl (id,k,d) -> Stmt.mk_decl ~info id k d
          | Stmt.Axiom (Stmt.Axiom_std l) -> Stmt.axiom ~info l
          | Stmt.Axiom (Stmt.Axiom_spec l) -> Stmt.axiom_spec ~info l
          | Stmt.Axiom (Stmt.Axiom_rec l) ->
              Stmt.axiom_rec ~info (Stmt.cast_rec_defs l)
          | Stmt.TyDef (k,l) -> Stmt.mk_ty_def ~info k l
          | Stmt.Goal g -> Stmt.goal ~info g)
    in
    pb', ()

  let decode_model ~state:_ m = m

  let pipe_with ~decode ~print =
    let on_encoded = if print
      then
        let module Ppb = Problem.Print(P)(P) in
        [Format.printf "@[<v2>after elimination of inductive predicates:@ %a@]@." Ppb.print]
      else []
    in
    Transform.make1
      ~name:"elim_ind_pred"
      ~on_encoded
      ~encode:(fun pb -> elim_ind_preds pb)
      ~decode
      ()

  let pipe ~print =
    pipe_with ~decode:(fun state m -> decode_model ~state m) ~print
end
