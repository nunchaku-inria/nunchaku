
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 FOL to Relational FO Logic} *)

open Nunchaku_core

let name = "fo_to_rel"

type state = unit

let encode_pb pb =
  let state = () in
  pb, state

let decode _state m = m

let pipe_with ~decode ~print =
  let on_encoded =
    Utils.singleton_if print () ~f:(fun () ->
      Format.printf "@[<2>@{<Yellow>after %s@}: %a@]@."
        name FO.print_problem)
  in
  Transform.make ~name ~on_encoded ~encode:encode_pb ~decode ()

let pipe ~print =
  pipe_with ~decode ~print

