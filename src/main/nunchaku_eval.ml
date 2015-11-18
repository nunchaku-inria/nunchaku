
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Evaluate the Goal} *)

module E = CCError
module A = NunUntypedAST
module T = NunTermTyped.Default

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

let main ~file =
  let module TyInfer = NunTypeInference.Convert(T) in
  let module ToEval = NunEvalOfTyped.Convert(T) in
  let module P = NunTermEval.Print in
  parse_file ~file ()
  >>=
  TyInfer.convert_problem ~env:TyInfer.empty_env
  >>= fun (pb, _) ->
  E.guard_str_trace (fun () -> ToEval.convert_pb pb)
  >>= fun (_env,goal) ->
  Format.printf "@[<2>evaluate `@[%a@]`@]@." P.print goal;
  let goal' = NunEvalUtils.whnf_term goal in
  Format.printf "@[<2>WHNF: `@[%a@]`@]@." P.print goal';
  E.return ()

(** {2 Main} *)

let file_ = ref ""
let options = Arg.align []

let () =
  Arg.parse options (fun s -> file_ := s) "usage: nunchaku_eval <file>";
  E.catch (main ~file:!file_)
    ~ok:(fun () -> ())
    ~err:(fun msg -> print_endline msg; exit 1)




