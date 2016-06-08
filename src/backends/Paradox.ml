
(* This file is free software, part of nunchaku. See file "license" for more details. *)

open Nunchaku_core

module T = FO_tptp
module Res = Problem.Res
module E = CCResult
module S = Scheduling
module Pa = Nunchaku_parsers
module A = Pa.TPTP_model_ast

let name = "paradox"
let section = Utils.Section.make name

let is_available () =
  try
    let res = Sys.command "which paradox > /dev/null" = 0 in
    if res then Utils.debug ~section 3 "CVC4 is available";
    res
  with Sys_error _ -> false

exception Error of string

let () = Printexc.register_printer
    (function
      | Error msg -> Some (Utils.err_sprintf "Paradox: %s" msg)
      | _ -> None)

let error_ msg = raise (Error msg)
let errorf msg = Utils.exn_ksprintf msg ~f:error_

let print_pb_ file pb =
  CCIO.with_out file
    (fun oc ->
       let fmt = Format.formatter_of_out_channel oc in
       Format.fprintf fmt "@[<v>%a@]@." T.print_problem_tptp pb)

let begin_model = "SZS output start FiniteModel"
let end_model = "SZS output end FiniteModel"

(* TODO : also include constants? e.g. on skolem_unique, skolem
  constants are not included in the model *)

(* parse a model from paradox' output [s] *)
let parse_model s =
  let i1 = CCString.find ~sub:begin_model s in
  let i1 = String.index_from s i1 '\n'+1 in (* skip full line *)
  let i2 = CCString.find ~start:i1 ~sub:end_model s in
  (* [s']: part of [s] between the model markers *)
  let s' = String.sub s i1 (i2-i1) in
  let lexbuf = Lexing.from_string s' in
  Location.set_file lexbuf "<paradox output>";
  let l =
    try
      Pa.TPTP_model_parser.parse_statement_list
        Pa.TPTP_model_lexer.token
        lexbuf
    with e ->
      errorf "@[<hv2>parsing model failed:@ %s@]" (Printexc.to_string e)
  in
  Utils.debugf ~section 3 "@[<2>parsed model:@ @[<hv>%a@]@]"
    (fun k->k A.pp_statements l);
  A.to_model l

(* [s] is the output of paradox, parse a result from it *)
let parse_res ~meta s =
  if CCString.mem ~sub:"BEGIN MODEL" s
  then if meta.ProblemMetadata.sat_means_unknown
    then Res.Unknown, S.No_shortcut
    else
      let m = parse_model s in
      Res.Sat m, S.Shortcut
  else if CCString.mem ~sub:"RESULT: Unsatisfiable" s
  then if meta.ProblemMetadata.unsat_means_unknown
    then Res.Unknown, S.No_shortcut
    else Res.Unsat, S.Shortcut
  else Res.Unknown, S.No_shortcut

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
           Printf.sprintf "ulimit -t %d; paradox --time %d --model --tstp '%s'"
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
           | S.Fut.Done (E.Ok (stdout, errcode)) ->
             Utils.debugf ~lock:true ~section 2
               "@[<2>paradox exited with %d, stdout:@ `%s`@]" (fun k->k errcode stdout);
             parse_res ~meta:pb.FO_tptp.pb_meta stdout
           | S.Fut.Done (E.Error e) ->
             Res.Error e, S.Shortcut
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
let call ?(print_model=false) ?prio ~print problem =
  if print
  then Format.printf "@[<v2>FO_tptp problem:@ %a@]@." T.print_problem_tptp problem;
  S.Task.make ?prio
    (fun ~deadline () ->
       let res, short = solve ~deadline problem in
       Utils.debugf ~section 2 "@[<2>paradox result:@ %a@]"
         (fun k->k Res.print_head res);
       begin match res with
         | Res.Sat m when print_model ->
           let pp_ty oc _ = CCFormat.string oc "$i" in
           Format.printf "@[<2>raw paradox model:@ @[%a@]@]@."
             (Model.print (CCFun.const T.print_term_tptp) pp_ty) m
         | _ -> ()
       end;
       res, short)

let pipe ?(print_model=false) ~print () =
  let encode pb =
    let prio = 25 in
    call ~print_model ~prio ~print pb, ()
  in
  Transform.make
    ~name ~encode ~decode:(fun _ x -> x) ()
