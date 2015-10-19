
(** {1 Main program} *)

module E = CCError
module A = NunUntypedAST
module Utils = NunUtils

type input =
  | I_nunchaku
  | I_tptp

let list_inputs_ () = "(available choices: nunchaku tptp)"

(** {2 Options} *)

let input_ = ref I_nunchaku
let print_ = ref false
let print_typed_ = ref false
let print_skolem_ = ref false
let print_mono_ = ref false
let print_fo_ = ref false
let print_smt_ = ref false
let timeout_ = ref 30
let version_ = ref false
let file = ref ""

let set_file f =
  if !file <> ""
  then raise (Arg.Bad "please provide only one file")
  else file := f

let set_input_ f =
  input_ := match String.lowercase f with
    | "nunchaku" -> I_nunchaku
    | "tptp" -> I_tptp
    | s -> failwith ("unsupported input format: " ^ s)

(* set debug levels *)
let options_debug_ = Utils.Section.iter
  |> Sequence.map
    (fun (name,sec) ->
      "--debug" ^ (if name="" then "" else "."^name),
      Arg.Int (Utils.Section.set_debug sec),
      " verbosity level for " ^ (if name="" then "all messages" else name))
  |> Sequence.to_rev_list

let options =
  let open CCFun in
  Arg.align ?limit:None @@ List.sort Pervasives.compare @@ (
  options_debug_ @
  [ "--print-input", Arg.Set print_, " print input"
  ; "--print-typed", Arg.Set print_typed_, " print input after typing"
  ; "--print-skolem", Arg.Set print_skolem_, " print input after Skolemization"
  ; "--print-mono", Arg.Set print_mono_, " print input after monomorphization"
  ; "--print-fo", Arg.Set print_fo_, " print first-order problem"
  ; "--print-smt", Arg.Set print_smt_, " print SMT problem"
  ; "--print-raw-model", Arg.Set NunSolver_intf.print_model_, " print raw model"
  ; "--timeout", Arg.Set_int timeout_, " set timeout (in s)"
  ; "--input", Arg.String set_input_, " set input format " ^ list_inputs_ ()
  ; "--backtrace", Arg.Unit (fun () -> Printexc.record_backtrace true), " enable stack traces"
  ; "--version", Arg.Set version_, " print version and exit"
  ]
)

let print_version_if_needed () =
  if !version_ then (
    Format.printf "nunchaku %s@." Const.version;
    exit 0
  );
  ()

let parse_file ~input () =
  let with_in f =
    if !file="" then f stdin
    else CCIO.with_in !file f
  in
  let res = with_in
    (fun ic ->
      let lexbuf = Lexing.from_channel ic in
      NunLocation.set_file lexbuf (if !file="" then "<stdin>" else !file);
      try
        let res = match input with
          | I_nunchaku -> NunParser.parse_statement_list NunLexer.token lexbuf
          | I_tptp -> NunTPTPParser.parse_statement_list NunTPTPLexer.token lexbuf
        in
        E.return res
      with e ->
        E.fail (Printexc.to_string e)
    )
  in
  E.map_err
    (fun msg -> CCFormat.sprintf "@[<2>could not parse `%s`:@ %s@]" !file msg) res

let print_input_if_needed statements =
  if !print_ then
    Format.printf "@[<2>input:@ {%a@]@,}@." A.print_statement_list statements;
  ()

(* build a pipeline, depending on options *)
let make_pipeline () =
  let open NunTransform.Pipe in
  (* type inference *)
  let step_ty_infer = NunTypeInference.pipe ~print:!print_typed_
    NunTerm_typed.default NunTerm_ho.default in
  (* encodings *)
  let step_skolem =
    NunSkolem.pipe ~print:!print_skolem_
    NunTerm_typed.as_ho NunTerm_ho.default in
  let step_monomorphization =
    NunMonomorphization.pipe ~print:!print_mono_ NunTerm_ho.default in
  (* conversion to FO *)
  let step_fo = NunTerm_ho.to_fo
    (module NunTerm_ho.Default) (module NunFO.Default)
  in
  (* setup pipeline *)
  let pipe =
    step_ty_infer @@@
    step_skolem @@@
    step_monomorphization @@@
    step_fo @@@
    id
  in
  let deadline = Utils.Time.start () +. (float_of_int !timeout_) in
  let module T = NunTerm_ho.AsFO(NunTerm_ho.Default) in
  NunCVC4.close_pipe (module T)
    ~pipe ~deadline ~print:!print_fo_ ~print_smt:!print_smt_

(* search for results *)
let rec traverse_list_ l =
  let module Res = NunProblem.Res in
  try
  match l() with
    | `Nil -> E.fail "exhausted possibilities"
    | `Cons ((res, conv_back), tail) ->
        match res with
        | Res.Timeout -> E.fail "timeout"
        | Res.Unsat -> traverse_list_ tail
        | Res.Sat m ->
            let m = conv_back m in
            E.return m
  with e -> NunUtils.err_of_exn e

(* main *)
let main () =
  let open CCError.Infix in
  Arg.parse options set_file "usage: nunchaku [options] file";
  print_version_if_needed ();
  (* parse *)
  parse_file ~input:!input_ ()
  >>= fun statements ->
  print_input_if_needed statements;
  (* run pipeline *)
  let cpipe = make_pipeline() in
  NunTransform.run_closed ~cpipe statements
  |> traverse_list_

let () =
  E.catch (main ())
    ~ok:(fun m ->
      Format.printf "@[<2>SAT:@ model {@,%a@]@,}@."
        (NunProblem.Model.print NunUntypedAST.print_term) m;
      exit 0
    )
    ~err:(fun msg ->
      Format.eprintf "%s@." msg;
      exit 1
    )
