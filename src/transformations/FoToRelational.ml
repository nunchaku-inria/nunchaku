
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 FOL to Relational FO Logic} *)

open Nunchaku_core

let name = "fo_to_rel"

type problem1 = (FO.T.t, FO.Ty.t) FO.Problem.t
type model1 = (FO.T.t, FO.Ty.t) Model.t

type problem2 = FO_rel.problem
type model2 = (FO_rel.expr, FO_rel.expr) Model.t

(** {2 Encoding} *)

type state = unit

let encode_pb pb =
  let state = () in
  let pb' = assert false in
  pb', state

(** {2 Decoding} *)

let decode _state m = assert false

(** {2 Pipes} *)

let pipe_with ~decode ~print =
  let on_encoded =
    Utils.singleton_if print () ~f:(fun () ->
      Format.printf "@[<2>@{<Yellow>after %s@}: %a@]@."
        name FO_rel.print_problem)
  in
  Transform.make ~name ~on_encoded ~encode:encode_pb ~decode ()

let pipe ~print =
  pipe_with ~decode ~print

