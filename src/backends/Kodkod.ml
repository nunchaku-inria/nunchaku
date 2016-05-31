
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Interface to Kodkod} *)

open Nunchaku_core

module Res = Problem.Res
module T = FO.T
module Ty = FO.Ty

let name = "kodkod"

type problem = (T.t, Ty.t) FO.Problem.t

type t = unit
(* TODO *)

let name = name

(* TODO *)
let res _ = Res.Error (Failure "not implemented")
let peek_res _ = None

(* TODO *)
let solve ?options:_ ?timeout ?print pb = ()

(* TODO *)
let close _ = ()

let call ?options ?timeout ?print pb =
  assert false (* TODO *)

let is_available () =
  try Sys.command "which kodkodki" = 0
  with Sys_error _ -> false

let pipe ?deadline ~print () =
  (* TODO: deadline *)
  let encode pb = call ~print pb in
  Transform.make
    ~name
    ~encode
    ~decode:(fun _ res -> res)
    ()
