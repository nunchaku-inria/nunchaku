
(* This file is free software, part of nunchaku. See file "license" for more details. *)

open Nunchaku_core

module T = FO_tptp
module Res = Problem.Res
module S = Scheduling

let name = "paradox"
let section = Utils.Section.make name

let is_available () =
  try
    let res = Sys.command "which paradox > /dev/null" = 0 in
    if res then Utils.debug ~section 3 "CVC4 is available";
    res
  with Sys_error _ -> false

let print_pb_ file pb =
  CCIO.with_out file
    (fun oc ->
       let fmt = Format.formatter_of_out_channel oc in
       Format.fprintf fmt "@[<v>%a@]@." T.print_problem_tptp pb)

let solve ~deadline pb =
  Utils.debug ~section 1 "calling paradox";
  let now = Unix.gettimeofday() in
  if now +. 0.5 > deadline
  then Res.Timeout, S.No_shortcut
  else (
    (* use a temporary file for calling paradox *)
    CCIO.File.with_temp ~prefix:"nunchaku_paradox" ~suffix:".p"
      (fun file ->
         Utils.debugf ~lock:true ~section 2
           "@[<2>use temporary file `%s`@]" (fun k->k file);
         (* print the problem *)
         print_pb_ file pb;
         let timeout = deadline -. now in
         let paradox_timeout = int_of_float (ceil (deadline -. now)) in
         let hard_timeout = (int_of_float (timeout +. 1.5)) in
         let cmd =
           Printf.sprintf "ulimit -t %d; paradox --time %d --model '%s'"
              hard_timeout paradox_timeout file
         in
         (* call paradox, get its stdout and errcode *)
         let fut =
           S.popen cmd
             ~f:(fun (stdin,stdout) ->
               close_out stdin;
               CCIO.read_all stdout)
         in
         match S.Fut.get fut with
           | S.Fut.Done (stdout, errcode) ->
             Utils.debugf ~lock:true ~section 2
               "@[<2>paradox exited with %d, stdout:@ `%s`@]" (fun k->k errcode stdout);
             assert false (* TODO *)
           | S.Fut.Stopped ->
             Res.Timeout, S.No_shortcut
           | S.Fut.Fail e ->
             (* return error *)
             Utils.debugf ~lock:true ~section 1 "@[<2>paradox failed with@ %s@]"
               (fun k->k (Printexc.to_string e));
             Res.Error e, S.Shortcut
      )
  )

(* solve problem before [deadline] *)
let call ?prio ~deadline ~print problem =
  if print
  then Format.printf "@[<v2>FO_tptp problem:@ %a@]@." T.print_problem_tptp problem;
  S.Task.make ?prio
    (fun () -> solve ~deadline problem)

let pipe ~deadline ~print () =
  let encode pb =
    let prio = 25 in
    call ~deadline ~prio ~print pb, ()
  in
  Transform.make
    ~name ~encode ~decode:(fun _ x -> x) ()
