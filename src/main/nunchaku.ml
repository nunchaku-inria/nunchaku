
(** {1 Main program} *)

open Nunchaku_core

module E = CCError
module A = UntypedAST
module Utils = Utils
module TI = TermInner
module CVC4 = Nunchaku_backends.CVC4

type input =
  | I_nunchaku
  | I_tptp

let list_inputs_ () = "(available choices: nunchaku tptp)"

type output =
  | O_nunchaku
  | O_tptp

let list_outputs_ () = "(available choices: nunchaku tptp)"

(** {2 Options} *)

let input_ = ref I_nunchaku
let output_ = ref O_nunchaku
let check_all_ = ref false
let polarize_rec_ = ref true
let print_ = ref false
let print_all_ = ref false
let print_pipeline_ = ref false
let print_typed_ = ref false
let print_skolem_ = ref false
let print_mono_ = ref false
let print_elim_match_ = ref false
let print_elim_recursion_ = ref false
let print_elim_hof_ = ref false
let print_lambda_lift_ = ref false
let print_specialize_ = ref false
let print_elim_multi_eqns = ref false
let print_polarize_ = ref false
let print_unroll_ = ref false
let print_elim_preds_ = ref false
let print_copy_ = ref false
let print_intro_guards_ = ref false
let print_fo_ = ref false
let print_smt_ = ref false
let print_raw_model_ = ref false
let print_model_ = ref false
let enable_polarize_ = ref true
let timeout_ = ref 30
let version_ = ref false
let file = ref ""
let j = ref 3

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

(* set debug levels *)
let options_debug_ = Utils.Section.iter
  |> Sequence.map
    (fun (name,sec) ->
      "--debug" ^ (if name="" then "" else "."^name),
      Arg.Int (Utils.Section.set_debug sec),
      " verbosity level for " ^ (if name="" then "all messages" else name))
  |> Sequence.to_rev_list

let call_with x f = Arg.Unit (fun () -> f x)

let options =
  let open CCFun in
  Arg.align ?limit:None @@ List.sort Pervasives.compare @@ (
  options_debug_ @
  Utils.options_warnings_ @
  [ "--print-input", Arg.Set print_, " print input"
  ; "--print-all", Arg.Set print_all_, " print every step of the pipeline"
  ; "--print-pipeline", Arg.Set print_pipeline_, " print full pipeline and exit"
  ; "--print-typed", Arg.Set print_typed_, " print input after typing"
  ; "--print-" ^ Skolem.name, Arg.Set print_skolem_, " print input after Skolemization"
  ; "--print-" ^ Monomorphization.name, Arg.Set print_mono_, " print input after monomorphization"
  ; "--print-" ^ ElimPatternMatch.name
      , Arg.Set print_elim_match_
      , " print input after elimination of pattern matching"
  ; "--print-" ^ ElimIndPreds.name
      , Arg.Set print_elim_preds_
      , " print input after elimination of (co)inductive predicates"
  ; "--print-" ^ ElimRecursion.name
      , Arg.Set print_elim_recursion_
      , " print input after elimination of recursive functions"
  ; "--print-" ^ Specialize.name
      , Arg.Set print_specialize_
      , " print input after specialization"
  ; "--print-" ^ LambdaLift.name, Arg.Set print_lambda_lift_, " print after λ-lifting"
  ; "--print-" ^ ElimHOF.name
      , Arg.Set print_elim_hof_
      , " print input after elimination of higher-order/partial functions"
  ; "--print-" ^ ElimMultipleEqns.name
      , Arg.Set print_elim_multi_eqns
      , " print input after elimination of multiple equations"
  ; "--print-" ^ Polarize.name , Arg.Set print_polarize_, " print input after polarization"
  ; "--print-" ^ Unroll.name, Arg.Set print_unroll_, " print input after unrolling"
  ; "--print-" ^ ElimCopy.name, Arg.Set print_copy_, " print input after elimination of copy types"
  ; "--print-" ^ IntroGuards.name, Arg.Set print_intro_guards_,
      " print input after introduction of guards"
  ; "--print-fo", Arg.Set print_fo_, " print first-order problem"
  ; "--print-smt", Arg.Set print_smt_, " print SMT problem"
  ; "--print-raw-model", Arg.Set print_raw_model_, " print raw model"
  ; "--print-model", Arg.Set print_model_, " print model after cleanup"
  ; "--print-undefined", Arg.Set TermInner.print_undefined_id, " print unique IDs of `undefined` terms"
  ; "--checks", Arg.Set check_all_, " check invariants after each pass"
  ; "--no-checks", Arg.Clear check_all_, " disable checking invariants after each pass"
  ; "--color", call_with true CCFormat.set_color_default, " enable color"
  ; "--no-color", call_with false CCFormat.set_color_default, " disable color"
  ; "-nc", call_with false CCFormat.set_color_default, " disable color (alias to --no-color)"
  ; "-j", Arg.Set_int j, " set parallelism level"
  ; "--polarize-rec", Arg.Set polarize_rec_, " enable polarization of rec predicates"
  ; "--no-polarize-rec", Arg.Clear polarize_rec_, " disable polarization of rec predicates"
  ; "--no-polarize", Arg.Clear enable_polarize_, " disable polarization"
  ; "--timeout", Arg.Set_int timeout_, " set timeout (in s)"
  ; "-t", Arg.Set_int timeout_, " alias to --timeout"
  ; "--input", Arg.String set_input_, " set input format " ^ list_inputs_ ()
  ; "-i", Arg.String set_input_, " synonym for --input"
  ; "--output", Arg.String set_output_, " set output format " ^ list_outputs_ ()
  ; "-o", Arg.String set_output_, " synonym for --output"
  ; "--backtrace", Arg.Unit (fun () -> Printexc.record_backtrace true), " enable stack traces"
  ; "--version", Arg.Set version_, " print version and exit"
  ]
)

let print_version_if_needed () =
  if !version_ then (
    Format.printf "nunchaku %s %s@." Const.version GitVersion.id;
    exit 0
  );
  ()

let parse_file ~input () =
  let open CCError.Infix in
  let src = if !file = "" then `Stdin else `File !file in
  let res =
    try
      match input with
      | I_nunchaku ->
          NunLexer.parse src
      | I_tptp ->
          NunTPTPLexer.parse ~mode:(`Env "TPTP") src
          >|= CCVector.to_seq
          >>= NunTPTPPreprocess.preprocess
    with e -> Utils.err_of_exn e
  in
  E.map_err
    (fun msg -> CCFormat.sprintf "@[<2>could not parse `%s`:@ %s@]" !file msg) res

let print_input_if_needed statements =
  if !print_ then
    Format.printf "@[<v2>input: {@,@[<v>%a@]@]@,}@."
      (CCVector.print ~start:"" ~stop:"" ~sep:"" A.print_statement)
      statements;
  ()

module Pipes = struct
  module HO = TI.Default
  module Typed = TermTyped.Default
  (* type inference *)
  module Step_tyinfer = TypeInference.Make(Typed)(HO)
  module Step_conv_ty = Problem.Convert(Typed)(HO)
  (* encodings *)
  module Step_skolem = Skolem.Make(HO)
  module Step_mono = Monomorphization.Make(HO)
  module Step_ElimMultipleEqns = ElimMultipleEqns.Make(HO)
  module Step_ElimMatch = ElimPatternMatch.Make(HO)
  module Step_ElimCodata = ElimData.Make_codata(HO)
  module Step_ElimPreds = ElimIndPreds.Make(HO)
  module Step_ElimData = ElimData.Make_data(HO)
  module Step_Specialize = Specialize.Make(HO)
  module Step_LambdaLift = LambdaLift.Make(HO)
  module Step_ElimHOF = ElimHOF.Make(HO)
  module Step_ElimRec = ElimRecursion.Make(HO)
  module Step_polarize = Polarize.Make(HO)
  module Step_unroll = Unroll.Make(HO)
  module Step_elim_copy = ElimCopy.Make(HO)
  module Step_intro_guards = IntroGuards.Make(HO)
  (* conversion to FO *)
  module Step_tofo = TermMono.TransFO(HO)
  (* renaming in model *)
  module Step_rename_model = Model_rename.Make(HO)
end

let close_task p =
  Transform.Pipe.close p
    ~f:(fun task ret ->
       Scheduling.Task.map ~f:ret task, CCFun.id)

(* build a pipeline, depending on options *)
let make_model_pipeline () =
  let open Transform.Pipe in
  let open Pipes in
  (* setup pipeline *)
  let check = !check_all_ in
  let deadline = Utils.Time.start () +. (float_of_int !timeout_) in
  let cvc4 =
    if CVC4.is_available ()
    then
      CVC4.pipes
        ~options:CVC4.options_l
        ~print:!print_all_
        ~print_smt:(!print_all_ || !print_smt_)
        ~print_model:(!print_all_ || !print_raw_model_)
        ~deadline ()
      @@@ id
    else Fail
  in
  let pipe =
    Step_tyinfer.pipe ~print:(!print_typed_ || !print_all_) @@@
    Step_conv_ty.pipe () @@@
    Step_skolem.pipe ~print:(!print_skolem_ || !print_all_) ~check ~mode:`Sk_types @@@
    Step_mono.pipe ~print:(!print_mono_ || !print_all_) ~check @@@
    Step_ElimMultipleEqns.pipe
      ~decode:(fun x->x) ~check
      ~print:(!print_elim_multi_eqns || !print_all_) @@@
    Step_Specialize.pipe ~print:(!print_specialize_ || !print_all_) ~check @@@
    (if !enable_polarize_
      then Step_polarize.pipe ~print:(!print_polarize_ || !print_all_)
        ~check ~polarize_rec:!polarize_rec_
      else Transform.nop ())
    @@@
    Step_unroll.pipe ~print:(!print_unroll_ || !print_all_) ~check @@@
    Step_skolem.pipe ~print:(!print_skolem_ || !print_all_) ~mode:`Sk_all ~check @@@
    Step_ElimPreds.pipe ~print:(!print_elim_preds_ || !print_all_) ~check @@@
    Step_elim_copy.pipe ~print:(!print_copy_ || !print_all_) ~check @@@
    Step_LambdaLift.pipe ~print:(!print_lambda_lift_ || !print_all_) ~check @@@
    Step_ElimHOF.pipe ~print:(!print_elim_hof_ || !print_all_) ~check @@@
    Step_ElimRec.pipe ~print:(!print_elim_recursion_ || !print_all_) ~check @@@
    Step_ElimMatch.pipe ~print:(!print_elim_match_ || !print_all_) ~check @@@
    Step_intro_guards.pipe ~print:(!print_intro_guards_ || !print_all_) ~check @@@
    Step_rename_model.pipe_rename ~print:(!print_model_ || !print_all_) @@@
    close_task (
      Step_tofo.pipe ~print:!print_all_ () @@@
      Transform.Pipe.flatten cvc4
    )
  in
  pipe

(* run the pipeline on this problem, then run tasks, and return the
   result *)
let run_tasks ~j pipe pb =
  let module Res = Problem.Res in
  let tasks =
    Transform.run ~pipe pb
    |> Lazy_list.map ~f:(fun (task,ret) -> Scheduling.Task.map ~f:ret task)
    |> Lazy_list.to_list
  in
  let res = Scheduling.run ~j tasks in
  match res with
  | Scheduling.Res_fail e -> E.fail (Printexc.to_string e)
  | Scheduling.Res_list [] -> E.fail "no task succeeded"
  | Scheduling.Res_list l ->
    assert
      (List.for_all
         (function
           | Res.Timeout | Res.Unknown -> true
           | Res.Error _ | Res.Sat _ | Res.Unsat -> false)
         l);
    let res = if List.mem Res.Timeout l then Res.Timeout else Res.Unknown in
    E.return res
  | Scheduling.Res_one r -> E.return r

(* negate the goal *)
let negate_goal stmts =
  let module A = UntypedAST in
  CCVector.map
    (fun st -> match st.A.stmt_value with
      | A.Goal f -> {st with A.stmt_value=A.Goal (A.not_ f); }
      | _ -> st)
    stmts

(* additional printers *)
let () = Printexc.register_printer
  (function
    | Failure msg -> Some ("failure: " ^ msg)
    | _ -> None)

(* model mode *)
let main_model ~output statements =
  let open CCError.Infix in
  let module T = TI.Default in
  let module P = TI.Print(T) in
  let module Res = Problem.Res in
  (* run pipeline *)
  let pipe = make_model_pipeline() in
  if !print_pipeline_
    then Format.printf "@[Pipeline: %a@]@." Transform.Pipe.print pipe;
  run_tasks ~j:!j pipe statements
  >|= fun res ->
  match res, output with
  | Res.Sat m, O_nunchaku when m.Model.potentially_spurious ->
      Format.printf "@[<v>@[<v2>SAT: (potentially spurious) {@,@[<v>%a@]@]@,}@]@."
        (Model.print P.print P.print) m;
  | Res.Sat m, O_nunchaku ->
      Format.printf "@[<v>@[<v2>SAT: {@,@[<v>%a@]@]@,}@]@."
        (Model.print P.print P.print) m;
  | Res.Sat m, O_tptp ->
      (* XXX: if potentially spurious, what should we print? *)
      let module PM = NunPrintTPTP.Make(T) in
      Format.printf "@[<v2>%a@]@,@." PM.print_model m
  | Res.Unsat, O_nunchaku ->
      Format.printf "@[UNSAT@]@."
  | Res.Unsat, O_tptp ->
      Format.printf "@[SZS Status: Unsatisfiable@]@."
  | Res.Unknown, _ ->
      Format.printf "@[UNKNOWN@]@."
  | Res.Timeout, _ ->
      Format.printf "@[TIMEOUT@]@."
  | Res.Error e, _ ->
      raise e

(* main *)
let main () =
  let open CCError.Infix in
  CCFormat.set_color_default true; (* default: enable colors *)
  Arg.parse options set_file "usage: nunchaku [options] file";
  print_version_if_needed ();
  if !print_pipeline_ then (
    let pipe = make_model_pipeline() in
    Format.printf "@[Pipeline: %a@]@." Transform.Pipe.print pipe;
    exit 0
  );
  (* parse *)
  parse_file ~input:!input_ ()
  >>= fun statements ->
  print_input_if_needed statements;
  main_model ~output:!output_ statements

let () =
  E.catch (try main () with e -> Utils.err_of_exn e)
  ~ok:(fun () -> exit 0)
  ~err:(fun msg ->
    Format.eprintf "%s@." msg;
    exit 1
  )
