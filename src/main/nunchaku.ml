
(** {1 Main program} *)

module E = CCError
module A = NunUntypedAST
module Utils = NunUtils

(** {2 Options} *)

let print_ = ref false
let print_typed_ = ref false
let print_fo_ = ref false
let timeout_ = ref 30
let version_ = ref false
let file = ref ""
let set_file f =
  if !file <> ""
  then raise (Arg.Bad "please provide only one file")
  else file := f

(* set debug levels *)
let options_debug_ = Utils.Section.iter
  |> Sequence.map
    (fun (name,sec) ->
      "--debug" ^ (if name="" then "" else "."^name),
      Arg.Int (Utils.Section.set_debug sec),
      " verbosity level for " ^ (if name="" then "all messages" else name))
  |> Sequence.to_rev_list

let options = Arg.align (
  options_debug_ @
  [ "--print", Arg.Set print_, " print input and exit"
  ; "--print-typed", Arg.Set print_typed_, " print input after typing"
  ; "--print-fo", Arg.Set print_fo_, " print first-order problem"
  ; "--timeout", Arg.Set_int timeout_, " set timeout (in s)"
  ; "--version", Arg.Set version_, " print version and exit"
  ]
)

let print_version_if_needed () =
  if !version_ then (
    Format.printf "nunchaku %s@." Const.version;
    exit 0
  );
  ()

let parse_file () =
  let res = if !file="" then  (
    Utils.debugf 1 "will read on stdin";
    NunLexer.parse_stdin ()
  ) else NunLexer.parse_file !file
  in
  E.map_err
    (fun msg -> Printf.sprintf "could not parse %s: %s" !file msg) res

let print_input_if_needed statements =
  if !print_ then (
    Format.printf "@[%a@]@." A.print_statement_list statements;
    exit 0
  );
  ()

(* build a pipeline, depending on options *)
let make_pipeline () =
  let open NunTransform.Pipe in
  (* type inference *)
  let step_ty_infer = Pipeline.ty_infer ~print:!print_typed_
    (module NunTerm_typed.Default) (module NunTerm_ho.Default) in
  (* encodings *)
  let step_monomorphization = Pipeline.mono ~print:false
    (module NunTerm_typed.Default) (module NunTerm_ho.Default) in
  (* conversion to FO *)
  let step_fo = Pipeline.to_fo
    (module NunTerm_ho.Default) (module NunFO.Default)
  in
  (* setup pipeline *)
  NunTransform.ClosedPipe.make1
    ~pipe:(
      step_ty_infer @@@
      step_monomorphization @@@
      step_fo @@@
      id
    )
    ~f:(
      (* timeout *)
      let deadline = Utils.Time.start () +. (float_of_int !timeout_) in
      let module T = NunTerm_ho.AsFO(NunTerm_ho.Default) in
      Pipeline.call_cvc4 (module T) ~deadline ~print:!print_fo_
    )

(* search for results *)
let rec traverse_list_ l =
  let module Res = Pipeline.Res in
  match l() with
  | `Nil -> E.fail "exhausted possibilities"
  | `Cons ((res, conv_back), tail) ->
      match res with
      | Res.Timeout -> E.fail "timeout"
      | Res.Unsat -> traverse_list_ tail
      | Res.Sat m ->
          let m = conv_back m in
          E.return m

(* main *)
let main () =
  let open CCError.Infix in
  Arg.parse options set_file "usage: nunchaku [options] file";
  print_version_if_needed ();
  Printexc.record_backtrace true;
  (* parse *)
  parse_file ()
  >>= fun statements ->
  print_input_if_needed statements;
  (* run pipeline *)
  let cpipe = make_pipeline() in
  NunTransform.run_closed ~cpipe statements
  |> traverse_list_

let () =
  E.catch (main ())
    ~ok:(fun m ->
      Format.printf "sat: model %a@."
        (NunProblem.Model.print NunUntypedAST.print_term) m;
      exit 0
    )
    ~err:(fun msg ->
      Format.eprintf "%s@." msg;
      exit 1
    )
