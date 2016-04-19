
(** {1 Main program} *)

open Nunchaku_core

module E = CCResult
module A = UntypedAST
module Utils = Utils
module TI = TermInner
module Backends = Nunchaku_backends
module Tr = Nunchaku_transformations

type input =
  | I_nunchaku
  | I_tptp

let inputs_ =
  [ "nunchaku", I_nunchaku
  ; "tptp", I_tptp
  ]

type output =
  | O_nunchaku
  | O_tptp
  | O_sexp

let outputs_ =
  [ "nunchaku", O_nunchaku
  ; "tptp", O_tptp
  ; "sexp", O_sexp
  ]

type solver =
  | S_CVC4
  | S_kodkod
  | S_paradox

let list_solvers_ () = "(available choices: cvc4 kodkod paradox)"

(** {2 Options} *)

let input_ = ref I_nunchaku
let output_ = ref O_nunchaku
let check_all_ = ref true
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
let print_elim_infinite = ref false
let print_elim_multi_eqns = ref false
let print_polarize_ = ref false
let print_unroll_ = ref false
let print_elim_preds_ = ref false
let print_elim_data_ = ref false
let print_copy_ = ref false
let print_intro_guards_ = ref false
let print_elim_ite_ = ref false
let print_elim_prop_args_ = ref false
let print_elim_types_ = ref false
let print_fo_ = ref false
let print_fo_to_rel_ = ref false
let print_smt_ = ref false
let print_raw_model_ = ref false
let print_model_ = ref false
let enable_polarize_ = ref true
let enable_specialize_ = ref true
let skolems_in_model_ = ref true
let timeout_ = ref 30
let version_ = ref false
let file = ref ""
let solvers = ref [S_CVC4; S_kodkod; S_paradox]
let j = ref 3
let prelude_ = ref []

let set_file f =
  if !file <> ""
  then raise (Arg.Bad "please provide only one file")
  else file := f

let add_prelude p = prelude_ := p :: !prelude_

let input_opt = Utils.arg_choice inputs_ ((:=) input_)
let output_opt = Utils.arg_choice outputs_ ((:=) output_)

(* solver string specification *)
let parse_solvers_ s =
  let s = String.trim s |> String.lowercase in
  let l = CCString.Split.list_cpy ~by:"," s in
  List.map
    (function
      | "cvc4" -> S_CVC4
      | "paradox" -> S_paradox
      | "kodkod" -> S_kodkod
      | s ->
        failwith (Utils.err_sprintf "unknown solver `%s` %s" s (list_solvers_())))
    l

let set_solvers_ s =
  let l = parse_solvers_ s |> CCList.Set.uniq ~eq:(=) in
  solvers := l

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
  ; "--print-" ^ Tr.Skolem.name, Arg.Set print_skolem_, " print input after Skolemization"
  ; "--print-" ^ Tr.Monomorphization.name, Arg.Set print_mono_, " print input after monomorphization"
  ; "--print-" ^ Tr.ElimPatternMatch.name
      , Arg.Set print_elim_match_
      , " print input after elimination of pattern matching"
  ; "--print-" ^ Tr.ElimIndPreds.name
      , Arg.Set print_elim_preds_
      , " print input after elimination of (co)inductive predicates"
  ; "--print-" ^ Tr.ElimRecursion.name
      , Arg.Set print_elim_recursion_
      , " print input after elimination of recursive functions"
  ; "--print-" ^ Tr.Specialize.name
      , Arg.Set print_specialize_
      , " print input after specialization"
  ; "--print-" ^ Tr.LambdaLift.name, Arg.Set print_lambda_lift_, " print after λ-lifting"
  ; "--print-" ^ Tr.ElimHOF.name
      , Arg.Set print_elim_hof_
      , " print input after elimination of higher-order/partial functions"
  ; "--print-" ^ Tr.ElimMultipleEqns.name
      , Arg.Set print_elim_multi_eqns
      , " print input after elimination of multiple equations"
  ; "--print-" ^ Tr.Elim_infinite.name
      , Arg.Set print_elim_infinite
      , " print input after elimination of infinite types"

  ; "--print-" ^ Tr.Polarize.name , Arg.Set print_polarize_, " print input after polarization"
  ; "--print-" ^ Tr.Unroll.name, Arg.Set print_unroll_, " print input after unrolling"
  ; "--print-" ^ Tr.ElimCopy.name, Arg.Set print_copy_, " print input after elimination of copy types"
  ; "--print-" ^ Tr.ElimData.name
      , Arg.Set print_elim_data_
      , " print input after elimination of (co)datatypes"
  ; "--print-" ^ Tr.IntroGuards.name, Arg.Set print_intro_guards_,
      " print input after introduction of guards"
  ; "--print-" ^ Tr.Elim_ite.name, Arg.Set print_elim_ite_,
      " print input after elimination of if/then/else"
  ; "--print-" ^ Tr.Elim_prop_args.name, Arg.Set print_elim_prop_args_,
      " print input after elimination of propositional function subterms"
  ; "--print-" ^ Tr.ElimTypes.name, Arg.Set print_elim_types_,
      " print input after elimination of types"
  ; "--print-fo", Arg.Set print_fo_, " print first-order problem"
  ; "--print-fo-to-rel", Arg.Set print_fo_to_rel_, " print first-order relational problem"
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
  ; "--no-specialize", Arg.Clear enable_specialize_, " disable specialization"
  ; "--skolems-in-model", Arg.Set skolems_in_model_, " enable skolem constants in models"
  ; "--no-skolems-in-model", Arg.Clear skolems_in_model_, " disable skolem constants in models"
  ; "--solvers", Arg.String set_solvers_, " solvers to use " ^ list_solvers_ ()
  ; "-s", Arg.String set_solvers_, " synonym for --solvers"
  ; "--timeout", Arg.Set_int timeout_, " set timeout (in s)"
  ; "-t", Arg.Set_int timeout_, " alias to --timeout"
  ; "--input", input_opt , " set input format"
  ; "-i", input_opt, " synonym for --input"
  ; "--output", output_opt, " set output format"
  ; "-o", output_opt, " synonym for --output"
  ; "--prelude", Arg.String add_prelude, " parse given prelude file"
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

let parse_file ~into ~input () =
  let open E.Infix in
  let src = if !file = "" then `Stdin else `File !file in
  let res =
    try
      match input with
      | I_nunchaku ->
          Nunchaku_parsers.Lexer.parse ~into src
          >|= CCVector.freeze
      | I_tptp ->
          Nunchaku_parsers.TPTP_lexer.parse ~into ~mode:(`Env "TPTP") src
          >|= CCVector.to_seq
          >>= Nunchaku_parsers.TPTP_preprocess.preprocess
    with e -> Utils.err_of_exn e
  in
  E.map_err
    (fun msg -> CCFormat.sprintf "@[<2>could not parse `%s`:@ %s@]" !file msg)
    res

(* parse list of prelude files *)
let parse_prelude files =
  let open E.Infix in
  let res = CCVector.of_list Prelude.decls in
  E.fold_l
    (fun () file ->
       Nunchaku_parsers.Lexer.parse (`File file) >|= fun vec ->
       CCVector.append res vec)
    ()
    files
  >|= fun () -> res

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
  module Step_tyinfer = Tr.TypeInference.Make(Typed)(HO)
  module Step_conv_ty = Problem.Convert(Typed)(HO)
  (* conversion to FO *)
  module Step_tofo = TermMono.TransFO(HO)
end

let close_task p =
  Transform.Pipe.close p
    ~f:(fun task ret ->
       Scheduling.Task.map ~f:ret task, CCFun.id)

let make_cvc4 ~j () =
  let open Transform.Pipe in
  if List.mem S_CVC4 !solvers && Backends.CVC4.is_available ()
  then
    Backends.CVC4.pipes
      ~options:Backends.CVC4.options_l
      ~slice:(1. *. float j)
      ~print:!print_all_
      ~print_smt:(!print_all_ || !print_smt_)
      ~print_model:(!print_all_ || !print_raw_model_)
      ()
    @@@ id
  else fail

let make_paradox () =
  let open Transform.Pipe in
  if List.mem S_paradox !solvers && Backends.Paradox.is_available ()
  then
    Backends.Paradox.pipe
      ~print_model:(!print_all_ || !print_raw_model_)
      ~print:!print_all_ ()
    @@@ id
  else fail

let make_kodkod () =
  let open Transform.Pipe in
  if List.mem S_kodkod !solvers && Backends.Kodkod.is_available ()
  then
    Backends.Kodkod.pipe
      ~print:!print_all_
      ~print_model:(!print_all_ || !print_raw_model_)
      ()
    @@@ id
  else fail

(* build a pipeline, depending on options *)
let make_model_pipeline () =
  let open Transform.Pipe in
  let open Pipes in
  (* setup pipeline *)
  let check = !check_all_ in
  (* solvers *)
  let cvc4 = make_cvc4 ~j:!j () in
  let paradox = make_paradox () in
  let kodkod = make_kodkod () in
  let pipe =
    Step_tyinfer.pipe ~print:(!print_typed_ || !print_all_) @@@
    Step_conv_ty.pipe () @@@
    Tr.Skolem.pipe
      ~skolems_in_model:!skolems_in_model_
      ~print:(!print_skolem_ || !print_all_) ~check ~mode:`Sk_types @@@
    Tr.Monomorphization.pipe ~print:(!print_mono_ || !print_all_) ~check @@@
    Tr.Elim_infinite.pipe ~print:(!print_elim_infinite || !print_all_) ~check @@@
    Tr.ElimCopy.pipe ~print:(!print_copy_ || !print_all_) ~check @@@
    Tr.ElimMultipleEqns.pipe
      ~decode:(fun x->x) ~check
      ~print:(!print_elim_multi_eqns || !print_all_) @@@
    (if !enable_specialize_
     then Tr.Specialize.pipe ~print:(!print_specialize_ || !print_all_) ~check
     else Transform.nop ())
    @@@
    (if !enable_polarize_
      then Tr.Polarize.pipe ~print:(!print_polarize_ || !print_all_)
        ~check ~polarize_rec:!polarize_rec_
      else Transform.nop ())
    @@@
    Tr.Unroll.pipe ~print:(!print_unroll_ || !print_all_) ~check @@@
    Tr.Skolem.pipe
      ~skolems_in_model:!skolems_in_model_
      ~print:(!print_skolem_ || !print_all_) ~mode:`Sk_all ~check @@@
    fork
      (
        Tr.ElimIndPreds.pipe ~print:(!print_elim_preds_ || !print_all_) ~check @@@
        Tr.ElimPatternMatch.pipe ~print:(!print_elim_match_ || !print_all_) ~check @@@
        Tr.ElimData.pipe ~print:(!print_elim_data_ || !print_all_) ~check @@@
        Tr.LambdaLift.pipe ~print:(!print_lambda_lift_ || !print_all_) ~check @@@
        Tr.ElimHOF.pipe ~print:(!print_elim_hof_ || !print_all_) ~check @@@
        Tr.ElimRecursion.pipe ~print:(!print_elim_recursion_ || !print_all_) ~check @@@
        Tr.IntroGuards.pipe ~print:(!print_intro_guards_ || !print_all_) ~check @@@
        fork
        ( Tr.Elim_prop_args.pipe ~print:(!print_elim_prop_args_ || !print_all_) ~check @@@
          Tr.ElimTypes.pipe ~print:(!print_elim_types_ || !print_all_) ~check @@@
          Tr.Model_rename.pipe_rename ~print:(!print_model_ || !print_all_) @@@
          close_task (
            Step_tofo.pipe ~print:!print_all_ () @@@
            Tr.Elim_ite.pipe ~print:(!print_elim_ite_ || !print_all_) @@@
            FO.pipe_tptp @@@
            paradox
          )
        )
        (
          Tr.Model_rename.pipe_rename ~print:(!print_model_ || !print_all_) @@@
          close_task (
            Step_tofo.pipe ~print:!print_all_ () @@@
            Tr.FoToRelational.pipe ~print:(!print_fo_to_rel_ || !print_all_) @@@
            kodkod
          ))
      )
      ( Tr.ElimIndPreds.pipe ~print:(!print_elim_preds_ || !print_all_) ~check @@@
        Tr.ElimCopy.pipe ~print:(!print_copy_ || !print_all_) ~check @@@
        Tr.LambdaLift.pipe ~print:(!print_lambda_lift_ || !print_all_) ~check @@@
        Tr.ElimHOF.pipe ~print:(!print_elim_hof_ || !print_all_) ~check @@@
        Tr.ElimRecursion.pipe ~print:(!print_elim_recursion_ || !print_all_) ~check @@@
        Tr.ElimPatternMatch.pipe ~print:(!print_elim_match_ || !print_all_) ~check @@@
        Tr.IntroGuards.pipe ~print:(!print_intro_guards_ || !print_all_) ~check @@@
        Tr.Model_rename.pipe_rename ~print:(!print_model_ || !print_all_) @@@
        close_task (
          Step_tofo.pipe ~print:!print_all_ () @@@
          Transform.Pipe.flatten cvc4
        )
      )
  in
  pipe

(* run the pipeline on this problem, then run tasks, and return the
   result *)
let run_tasks ~j ~deadline pipe pb =
  let module Res = Problem.Res in
  let tasks =
    Transform.run ~pipe pb
    |> Lazy_list.map ~f:(fun (task,ret) -> Scheduling.Task.map ~f:ret task)
    |> Lazy_list.to_list
  in
  let res = Scheduling.run ~j ~deadline tasks in
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
  let open E.Infix in
  let module T = TI.Default in
  let module P = TI.Print(T) in
  let module Res = Problem.Res in
  (* run pipeline *)
  let pipe = make_model_pipeline() in
  Transform.Pipe.check pipe;
  assert (not !print_pipeline_);
  let deadline = Utils.Time.start () +. (float_of_int !timeout_) in
  run_tasks ~j:!j ~deadline pipe statements
  >|= fun res ->
  match res, output with
  | _, O_sexp ->
      let s = Problem.Res.to_sexp P.to_sexp P.to_sexp res in
      Format.printf "@[<hv2>%a@]@." CCSexpM.print s
  | Res.Sat m, O_nunchaku when m.Model.potentially_spurious ->
      Format.printf "@[<v>@[<v2>SAT: (potentially spurious) {@,@[<v>%a@]@]@,}@]@."
        (Model.print P.print' P.print) m;
  | Res.Sat m, O_nunchaku ->
      Format.printf "@[<v>@[<v2>SAT: {@,@[<v>%a@]@]@,}@]@."
        (Model.print P.print' P.print) m;
  | Res.Sat m, O_tptp ->
      (* XXX: if potentially spurious, what should we print? *)
      let module PM = Nunchaku_parsers.TPTP_print.Make(T) in
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
  let open E.Infix in
  CCFormat.set_color_default true; (* default: enable colors *)
  Arg.parse options set_file "usage: nunchaku [options] file";
  print_version_if_needed ();
  if !print_pipeline_ then (
    let pipe = make_model_pipeline() in
    Format.printf "@[Pipeline: %a@]@." Transform.Pipe.print pipe;
    Transform.Pipe.check pipe;
    exit 0
  );
  (* parse *)
  parse_prelude (List.rev !prelude_)
  >>= fun statements ->
  parse_file ~into:statements ~input:!input_ ()
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
