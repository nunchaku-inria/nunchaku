
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Evaluate the Goal} *)

module E = CCError
module A = NunUntypedAST
module T = NunTermTyped.Default
module HO = NunTermInner.Default

open E.Infix

let parse_file ~file () =
  let with_in f =
    if file="" then f stdin
    else CCIO.with_in file f
  in
  let res = with_in
    (fun ic ->
      let lexbuf = Lexing.from_channel ic in
      NunLocation.set_file lexbuf (if file="" then "<stdin>" else file);
      try
        E.return (NunParser.parse_statement_list NunLexer.token lexbuf)
      with e -> E.fail (Printexc.to_string e)
    )
  in
  E.map_err
    (fun msg -> CCFormat.sprintf "@[<2>could not parse `%s`:@ %s@]" file msg) res

let pipe =
  let open NunTransform.Pipe in
  let module TyInfer = NunTypeInference.Make(T)(HO) in
  let module Conv = NunProblem.Convert(T)(HO) in
  let module Uniq = NunElimMultipleEqns.Make(HO) in
  let step_ty_infer = TyInfer.pipe_with ~decode:(fun ~signature:_ x -> x) ~print:true in
  let step_conv = Conv.pipe () in
  let step_uniq_eqn = Uniq.pipe ~decode:(fun ()->()) ~print:true in
  (* encodings *)
  step_ty_infer @@@
  step_conv @@@
  step_uniq_eqn @@@
  id

let main ~file =
  let module P = NunTermEval.Print in
  let module ToEval = NunEvalOfPoly.Convert(HO) in (* TODO: move it to pipe *)
  parse_file ~file ()
  >>= fun pb ->
  let pb, _ = CCKList.head_exn (NunTransform.run ~pipe pb) in
  E.guard_str_trace (fun () -> ToEval.convert_pb pb)
  >>= fun (_env,goal) ->
  Format.printf "@[<2>evaluate `@[%a@]`@]@." P.print goal;
  let goal' = NunEvalUtils.whnf_term goal in
  Format.printf "@[<2>WHNF: `@[%a@]`@]@." P.print goal';
  E.return ()

(** {2 Main} *)

let file_ = ref ""
let options = Arg.align
  [ "--debug", Arg.Int NunUtils.set_debug, " debug level"
  ; "--backtrace", Arg.Unit (fun () -> Printexc.record_backtrace true),
      " enable stack traces"
  ]

let () =
  Arg.parse options (fun s -> file_ := s) "usage: nunchaku_eval <file>";
  E.catch (main ~file:!file_)
    ~ok:(fun () -> ())
    ~err:(fun msg -> print_endline msg; exit 1)




