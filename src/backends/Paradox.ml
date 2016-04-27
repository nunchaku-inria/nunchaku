
(* This file is free software, part of nunchaku. See file "license" for more details. *)

open Nunchaku_core

module T = FO_tptp

let name = "paradox"
let section = Utils.Section.make name

let is_available () =
  try
    let res = Sys.command "which paradox > /dev/null" = 0 in
    if res then Utils.debug ~section 3 "CVC4 is available";
    res
  with Sys_error _ -> false

let solve ?deadline pb =
  assert false (* TODO *)

(* solve problem before [deadline] *)
let call
    ?deadline ?prio ~print problem
  =
  if print
  then Format.printf "@[<v2>FO_tptp problem:@ %a@]@." T.print_problem_tptp problem;
  Scheduling.Task.of_fut ?prio
    (fun () -> solve ?deadline problem)

let pipe ?deadline ~print () =
  let encode pb =
    let prio = 25 in
    call ?deadline ~prio ~print pb, ()
  in
  Transform.make
    ~name ~encode ~decode:(fun _ x -> x) ()
