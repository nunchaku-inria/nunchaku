
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Polarize} *)

module TI = TermInner
module Stmt = Statement

type ('a,'b) inv = <ty:[`Mono]; eqn:'a; ind_preds:'b>

module Make(T : TI.S) = struct
  module P = TI.Print(T)

  type term = T.t
  type decode_state = unit

  let elim_ind_preds
  : (term, term, ('a,'b) inv) Problem.t ->
    (term, term, ('a,'b) inv) Problem.t * decode_state
  = fun pb ->
    let pb' = Problem.map_statements pb
      ~f:(fun st ->
          let info = Stmt.info st in
          match Stmt.view st with
          | Stmt.Pred _ -> assert false
          | Stmt.Decl (id,k,d) -> Stmt.mk_decl ~info id k d
          | Stmt.Axiom l ->
              assert false (* TODO: find how to cast! *)
              (* Stmt.mk_axiom ~info l *)
          | Stmt.TyDef (k,l) -> Stmt.mk_ty_def ~info k l
          | Stmt.Goal g -> Stmt.goal ~info g)
    in
    pb', ()

  let decode_model ~state:_ m = m

  let pipe_with ~decode ~print =
    let on_encoded = if print
      then
        let module Ppb = Problem.Print(P)(P) in
        [Format.printf "@[<v2>after polarization:@ %a@]@." Ppb.print]
      else []
    in
    Transform.make1
      ~name:"polarize"
      ~on_encoded
      ~encode:(fun pb -> elim_ind_preds pb)
      ~decode
      ()

  let pipe ~print =
    pipe_with ~decode:(fun state m -> decode_model ~state m) ~print
end

