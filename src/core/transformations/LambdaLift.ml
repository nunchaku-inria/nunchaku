
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Lambda Lifting} *)

module TI = TermInner

type inv = <ty:[`Mono]; ind_preds:[`Absent]; eqn:[`Single]>

let name = "lambda_lift"

module Make(T : TI.S) = struct
  module T = T
  module U = TI.Util(T)
  module P = TI.Print(T)

  type state = unit (* TODO *)

  let create_state () = ()

  (* TODO *)
  let tr_problem ~state:_ pb = pb

  (* TODO *)
  let decode_model ~state:_ m = m

  let pipe_with ~decode ~print ~check =
    let on_encoded =
      Utils.singleton_if print ()
        ~f:(fun () ->
          let module Ppb = Problem.Print(P)(P) in
          Format.printf "@[<v2>@{<Yellow>after λ-lifting@}: %a@]@." Ppb.print)
      @
      Utils.singleton_if check ()
        ~f:(fun () ->
           let module C = TypeCheck.Make(T) in
           C.check_problem ?env:None)
    in
    Transform.make1
      ~name
      ~on_encoded
      ~encode:(fun pb ->
        let state = create_state () in
        let pb = tr_problem ~state pb in
        pb, state
      )
      ~decode
      ()

  let pipe ~print ~check =
    pipe_with ~check ~decode:(fun state m -> decode_model ~state m) ~print
end

