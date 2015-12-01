
(** {1 Main program} *)

module E = CCError
module A = UntypedAST
module Utils = Utils
module TI = TermInner

type input =
  | I_nunchaku
  | I_tptp

let list_inputs_ () = "(available choices: nunchaku tptp)"

type output =
  | O_nunchaku
  | O_tptp

let list_outputs_ () = "(available choices: nunchaku tptp)"

type mode =
  | M_model
  | M_proof

let list_modes_ () = "(available choices: model proof)"

(** {2 Options} *)

let mode_ = ref M_model
let input_ = ref I_nunchaku
let output_ = ref O_nunchaku
let print_ = ref false
let print_pipeline_ = ref false
let print_typed_ = ref false
let print_skolem_ = ref false
let print_mono_ = ref false
let print_elim_match_ = ref false
let print_recursion_elim_ = ref false
let print_elim_multi_eqns = ref false
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

let set_output_ f =
  output_ := match String.lowercase f with
    | "nunchaku" -> O_nunchaku
    | "tptp" -> O_tptp
    | s -> failwith ("unsupported output format: " ^ s)

let set_mode_ f =
  mode_ := match String.lowercase f with
    | "model" -> M_model
    | "proof" -> M_proof
    | s -> failwith ("unsupported mode: " ^ s)

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
  ; "--print-pipeline", Arg.Set print_pipeline_, " print full pipeline"
  ; "--print-typed", Arg.Set print_typed_, " print input after typing"
  ; "--print-skolem", Arg.Set print_skolem_, " print input after Skolemization"
  ; "--print-mono", Arg.Set print_mono_, " print input after monomorphization"
  ; "--print-elim-match", Arg.Set print_elim_match_,
      " print input after elimination of pattern matching"
  ; "--print-rec-elim", Arg.Set print_recursion_elim_,
      " print input after elimination of recursive functions"
  ; "--print-elim-multi-eqns", Arg.Set print_elim_multi_eqns,
      " print input after elimination of multiple equations"
  ; "--print-fo", Arg.Set print_fo_, " print first-order problem"
  ; "--print-smt", Arg.Set print_smt_, " print SMT problem"
  ; "--print-raw-model", Arg.Set Solver_intf.print_model_, " print raw model"
  ; "--timeout", Arg.Set_int timeout_, " set timeout (in s)"
  ; "--input", Arg.String set_input_, " set input format " ^ list_inputs_ ()
  ; "--output", Arg.String set_output_, " set output format " ^ list_outputs_ ()
  ; "--mode", Arg.String set_mode_, " search mode" ^ list_modes_ ()
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
      Location.set_file lexbuf (if !file="" then "<stdin>" else !file);
      try
        let res = match input with
          | I_nunchaku -> NunParser.parse_statement_list NunLexer.token lexbuf
          | I_tptp ->
              NunTPTPRecursiveParser.parse_statement_list NunTPTPLexer.token lexbuf
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
    Format.printf "@[<v2>input: {@,%a@]@,}@." A.print_statement_list statements;
  ()

(* build a pipeline, depending on options *)
let make_model_pipeline () =
  let open Transform.Pipe in
  let module HO = TI.Default in
  let module Typed = TermTyped.Default in
  (* type inference *)
  let module Step_tyinfer = TypeInference.Make(Typed)(HO) in
  let step_ty_infer = Step_tyinfer.pipe ~print:!print_typed_ in
  (* encodings *)
  let module Step_skolem = Skolem.Make(Typed)(HO) in
  let step_skolem = Step_skolem.pipe ~print:!print_skolem_ in
  let module Step_mono = Monomorphization.Make(HO) in
  let step_monomorphization = Step_mono.pipe ~print:!print_mono_ in
  let module Step_ElimMultipleEqns = ElimMultipleEqns.Make(HO) in
  let step_elim_multi_eqns = Step_ElimMultipleEqns.pipe
    ~decode:(fun x->x) ~print:!print_elim_multi_eqns in
  let module Step_ElimMatch = ElimPatternMatch.Make(HO) in
  let step_elim_match = Step_ElimMatch.pipe ~print:!print_elim_match_ in
  let module Step_rec_elim = ElimRecursion.Make(HO) in
  let step_recursion_elim = Step_rec_elim.pipe ~print:!print_recursion_elim_ in
  (* conversion to FO *)
  let module Step_tofo = TermMono.TransFO(HO)(FO.Default) in
  let step_fo = Step_tofo.pipe () in
  (* setup pipeline *)
  let pipe =
    step_ty_infer @@@
    step_skolem @@@
    step_monomorphization @@@
    step_elim_multi_eqns @@@
    step_recursion_elim @@@
    step_elim_match @@@
    step_fo @@@
    id
  in
  let deadline = Utils.Time.start () +. (float_of_int !timeout_) in
  CVC4.close_pipe FO.default
    ~pipe ~deadline ~print:!print_fo_ ~print_smt:!print_smt_

let make_proof_pipeline () =
  let open Transform.Pipe in
  let module HO = TI.Default in
  let module Typed = TermTyped.Default in
  (* type inference *)
  let module Step_tyinfer = TypeInference.Make(Typed)(HO) in
  let step_ty_infer = Step_tyinfer.pipe_with
    ~decode:(fun ~signature:_ x->x) ~print:!print_typed_ in
  (* encodings *)
  let module Step_skolem = Skolem.Make(Typed)(HO) in
  let step_skolem = Step_skolem.pipe_with
     ~decode:(fun _ x->x) ~print:!print_skolem_ in
  let module Step_mono = Monomorphization.Make(HO) in
  let step_monomorphization = Step_mono.pipe_with
    ~decode:(fun _ x -> x) ~print:!print_mono_ in
  let module Step_ElimMultipleEqns = ElimMultipleEqns.Make(HO) in
  let step_elim_multi_eqns = Step_ElimMultipleEqns.pipe
    ~decode:(fun x->x) ~print:!print_elim_multi_eqns in
  let module Step_ElimMatch = ElimPatternMatch.Make(HO) in
  let step_elim_match = Step_ElimMatch.pipe ~print:!print_elim_match_ in
  let module Step_rec_elim = ElimRecursion.Make(HO) in
  let step_recursion_elim = Step_rec_elim.pipe_with
    ~decode:(fun _ x -> x) ~print:!print_recursion_elim_ in
  (* conversion to FO *)
  let module Step_tofo = TermMono.TransFO(HO)(FO.Default) in
  let step_fo = Step_tofo.pipe_with ~decode:(fun x->x) in
  (* setup pipeline *)
  let pipe =
    step_ty_infer @@@
    step_skolem @@@
    step_monomorphization @@@
    step_elim_multi_eqns @@@
    step_recursion_elim @@@
    step_elim_match @@@
    step_fo @@@
    id
  in
  let deadline = Utils.Time.start () +. (float_of_int !timeout_) in
  CVC4.close_pipe FO.default
    ~pipe ~deadline ~print:!print_fo_ ~print_smt:!print_smt_

(* search for results *)
let rec find_model_ l =
  let module Res = Problem.Res in
  try
  match l() with
    | `Nil -> E.return `Unsat
    | `Cons ((res, conv_back), tail) ->
        match res with
        | Res.Timeout -> E.return `Timeout
        | Res.Unsat -> find_model_ tail
        | Res.Sat m ->
            let m = conv_back m in
            E.return (`Sat m)
  with e -> Utils.err_of_exn e

(* negate the goal *)
let negate_goal stmts =
  let module A = UntypedAST in
  CCList.map
    (fun st -> match st.A.stmt_value with
      | A.Goal f -> {st with A.stmt_value=A.Goal (A.not_ f); }
      | _ -> st
    ) stmts

type proof_output =
  | Unsat
  | Sat

(* look at the first result *)
let find_proof_ l =
  let module Res = Problem.Res in
  try
  match l() with
    | `Nil -> E.fail "exhausted possibilities"
    | `Cons ((res, _), _) ->
        match res with
        | Res.Timeout -> E.fail "timeout"
        | Res.Unsat -> E.return Unsat
        | Res.Sat _ -> E.return Sat
  with e -> Utils.err_of_exn e

(* additional printers *)
let () = Printexc.register_printer
  (function
    | Failure msg -> Some ("failure: " ^ msg)
    | _ -> None
  )

open CCError.Infix

(* model mode *)
let main_model ~output statements =
  (* run pipeline *)
  let cpipe = make_model_pipeline() in
  if !print_pipeline_
    then Format.printf "@[Pipeline: %a@]@." Transform.ClosedPipe.print cpipe;
  Transform.run_closed ~cpipe statements |> find_model_
  >|= fun res ->
  begin match res, output with
  | `Sat m, O_nunchaku ->
      Format.printf "@[<v2>SAT: @,%a@]@."
        (Model.print UntypedAST.print_term) m;
  | `Sat m, O_tptp ->
      Format.printf "@[<v2>%a@]@,@." NunPrintTPTP.print_model m
  | `Unsat, O_nunchaku ->
      (* TODO: check whether we have a "spurious" flag *)
      Format.printf "@[UNSAT@]"
  | `Unsat, O_tptp ->
      (* TODO: check whether we have a "spurious" flag *)
      Format.printf "@[SZS Status: Unsatisfiable@]@."
  | `Timeout, _ ->
      Format.printf "@[TIMEOUT@]@."
  end;
  ()

(* proof mode *)
let main_proof statements =
  (* run pipeline *)
  let cpipe = make_proof_pipeline () in
  if !print_pipeline_
    then Format.printf "@[Pipeline: %a@]@." Transform.ClosedPipe.print cpipe;
  let statements = negate_goal statements in
  Transform.run_closed ~cpipe statements |> find_proof_
  >|= fun res ->
  begin match res with
    | Unsat -> Format.printf "unsat@."
    | Sat -> Format.printf "sat@."
  end;
  ()

(* main *)
let main () =
  Arg.parse options set_file "usage: nunchaku [options] file";
  print_version_if_needed ();
  (* parse *)
  parse_file ~input:!input_ ()
  >>= fun statements ->
  print_input_if_needed statements;
  match !mode_ with
  | M_model -> main_model ~output:!output_ statements
  | M_proof -> main_proof statements

let () =
  E.catch (main ())
  ~ok:(fun () -> exit 0)
  ~err:(fun msg ->
    Format.eprintf "%s@." msg;
    exit 1
  )
