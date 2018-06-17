
(** {1 Main program} *)

open Nunchaku_core

module E = CCResult
module A = UntypedAST
module TI = TermInner
module Backends = Nunchaku_backends
module Tr = Nunchaku_transformations

type input =
  | I_guess
  | I_nunchaku
  | I_tptp
  | I_tip

let inputs_ =
  [ "nunchaku", I_nunchaku
  ; "tptp", I_tptp
  ; "tip", I_tip
  ]

(* TODO: tip output? *)

type output =
  | O_nunchaku
  | O_tptp
  | O_sexp

let outputs_ =
  [ "nunchaku", O_nunchaku
  ; "tptp", O_tptp
  ; "sexp", O_sexp
  ]

(* NOTE: also modify list_solvers_ below if you modify this *)
type solver =
  | S_CVC4
  | S_kodkod
  | S_paradox
  | S_smbc

let list_solvers_ () = "(available choices: cvc4 kodkod paradox smbc)"

(** {2 Options} *)

let input_ = ref I_guess
let output_ = ref O_nunchaku
let check_all_ = ref true
let polarize_rec_ = ref false
let pp_ = ref false
let pp_all_ = ref false
let pp_pipeline_ = ref false
let pp_typed_ = ref false
let pp_skolem_ = ref false
let pp_mono_ = ref false
let pp_elim_match_ = ref false
let pp_elim_recursion_ = ref false
let pp_elim_hof_ = ref false
let pp_lambda_lift_ = ref false
let pp_specialize_ = ref false
let pp_elim_infinite = ref false
let pp_elim_multi_eqns = ref false
let pp_polarize_ = ref false
let pp_unroll_ = ref false
let pp_elim_preds_ = ref false
let pp_cstor_as_fun_ = ref false
let pp_elim_data_ = ref false
let pp_elim_codata_ = ref false
let pp_copy_ = ref false
let pp_intro_guards_ = ref false
let pp_elim_ite_ = ref false
let pp_elim_prop_args_ = ref false
let pp_elim_types_ = ref false
let pp_fo_ = ref false
let pp_fo_to_rel_ = ref false
let pp_smt_ = ref false
let pp_raw_model_ = ref false
let pp_model_ = ref false
let enable_polarize_ = ref true
let enable_specialize_ = ref true
let skolems_in_model_ = ref true
let cvc4_schedule_ = ref true
let kodkod_min_bound_ = ref Backends.Kodkod.default_min_size
let kodkod_max_bound_ = ref None
let kodkod_bound_increment_ = ref Backends.Kodkod.default_size_increment
let timeout_ = ref 30
let version_ = ref false
let dump_ : [`No | `Yes | `Into of string] ref = ref `No
let file = ref ""
let solvers = ref [S_CVC4; S_kodkod; S_paradox; S_smbc]
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
  let s = String.trim s |> CCString.lowercase_ascii in
  let l = CCString.Split.list_cpy ~by:"," s in
  List.map
    (function
      | "cvc4" -> S_CVC4
      | "paradox" -> S_paradox
      | "kodkod" -> S_kodkod
      | "smbc" -> S_smbc
      | s ->
        failwith (Utils.err_sprintf "unknown solver `%s` %s" s (list_solvers_())))
    l

let set_solvers_ s =
  let l = parse_solvers_ s |> CCList.uniq ~eq:(=) in
  solvers := l

let set_dump () = dump_ := `Yes
let set_dump_into s = dump_ := `Into s

let call_with x f = Arg.Unit (fun () -> f x)

let options =
  let open CCFun in
  Arg.align @@ List.sort Pervasives.compare @@ (
    Utils.Options.get_all () @
      [ "--pp-input", Arg.Set pp_, " print input"
      ; "--pp-all", Arg.Set pp_all_, " print every step of the pipeline"
      ; "--pp-pipeline", Arg.Set pp_pipeline_, " print full pipeline and exit"
      ; "--pp-typed", Arg.Set pp_typed_, " print input after typing"
      ; "--pp-" ^ Tr.Skolem.name, Arg.Set pp_skolem_, " print input after Skolemization"
      ; "--pp-" ^ Tr.Monomorphization.name, Arg.Set pp_mono_, " print input after monomorphization"
      ; "--pp-" ^ Tr.ElimPatternMatch.name
      , Arg.Set pp_elim_match_
      , " print input after elimination of pattern matching"
      ; "--pp-" ^ Tr.ElimIndPreds.name
      , Arg.Set pp_elim_preds_
      , " print input after elimination of (co)inductive predicates"
      ; "--pp-" ^ Tr.ElimRecursion.name
      , Arg.Set pp_elim_recursion_
      , " print input after elimination of recursive functions"
      ; "--pp-" ^ Tr.Specialize.name
      , Arg.Set pp_specialize_
      , " print input after specialization"
      ; "--pp-" ^ Tr.LambdaLift.name, Arg.Set pp_lambda_lift_, " print after λ-lifting"
      ; "--pp-" ^ Tr.Cstor_as_fun.long_name
        , Arg.Set pp_cstor_as_fun_
        , " print input after removal of partial applications of constructors"
      ; "--pp-" ^ Tr.Elim_HOF.name
      , Arg.Set pp_elim_hof_
      , " print input after elimination of higher-order/partial functions"
      ; "--pp-" ^ Tr.ElimMultipleEqns.name
      , Arg.Set pp_elim_multi_eqns
      , " print input after elimination of multiple equations"
      ; "--pp-" ^ Tr.Elim_infinite.name
      , Arg.Set pp_elim_infinite
      , " print input after elimination of infinite types"

      ; "--pp-" ^ Tr.Polarize.name , Arg.Set pp_polarize_, " print input after polarization"
      ; "--pp-" ^ Tr.Unroll.name, Arg.Set pp_unroll_, " print input after unrolling"
      ; "--pp-" ^ Tr.ElimCopy.name, Arg.Set pp_copy_, " print input after elimination of copy types"
      ; "--pp-" ^ Tr.ElimData.Data.name
      , Arg.Set pp_elim_data_
      , " print input after elimination of (co)datatypes"
      ; "--pp-" ^ Tr.ElimData.Codata.name
      , Arg.Set pp_elim_codata_
      , " print input after elimination of (co)datatypes"
      ; "--pp-" ^ Tr.IntroGuards.name, Arg.Set pp_intro_guards_,
        " print input after introduction of guards"
      ; "--pp-" ^ Tr.Elim_ite.name, Arg.Set pp_elim_ite_,
        " print input after elimination of if/then/else"
      ; "--pp-" ^ Tr.Elim_prop_args.name, Arg.Set pp_elim_prop_args_,
        " print input after elimination of propositional function subterms"
      ; "--pp-" ^ Tr.ElimTypes.name, Arg.Set pp_elim_types_,
        " print input after elimination of types"
      ; "--pp-fo", Arg.Set pp_fo_, " print first-order problem"
      ; "--pp-" ^ Tr.FoToRelational.name, Arg.Set pp_fo_to_rel_,
        " print first-order relational problem"
      ; "--pp-smt", Arg.Set pp_smt_, " print SMT problem"
      ; "--pp-raw-model", Arg.Set pp_raw_model_, " print raw model"
      ; "--pp-model", Arg.Set pp_model_, " print model after cleanup"
      ; "--checks", Arg.Set check_all_, " check invariants after each pass"
      ; "--no-checks", Arg.Clear check_all_, " disable checking invariants after each pass"
      ; "--color", call_with true CCFormat.set_color_default, " enable color"
      ; "--no-color", call_with false CCFormat.set_color_default, " disable color"
      ; "-nc", call_with false CCFormat.set_color_default, " disable color (alias to --no-color)"
      ; "-j", Arg.Set_int j, " set parallelism level"
      ; "--dump", Arg.Unit set_dump, " instead of running solvers, dump their problem into files"
      ; "--dump-into",
        Arg.String set_dump_into,
        " instead of running solvers, dump their problem into files in <directory>"
      ; "--polarize-rec", Arg.Set polarize_rec_, " enable polarization of rec predicates"
      ; "--no-polarize-rec", Arg.Clear polarize_rec_, " disable polarization of rec predicates"
      ; "--no-polarize", Arg.Clear enable_polarize_, " disable polarization"
      ; "--no-specialize", Arg.Clear enable_specialize_, " disable specialization"
      ; "--skolems-in-model", Arg.Set skolems_in_model_, " enable skolem constants in models"
      ; "--no-skolems-in-model", Arg.Clear skolems_in_model_, " disable skolem constants in models"
      ; "--cvc4-schedule", Arg.Set cvc4_schedule_, " enable scheduling of multiple CVC4 instances"
      ; "--no-cvc4-schedule", Arg.Clear cvc4_schedule_,
        " disable scheduling of multiple CVC4 instances"
      ; "--kodkod-min-bound", Arg.Set_int kodkod_min_bound_,
        " set lower cardinality bound for Kodkod"
      ; "--kodkod-max-bound", Arg.Int (fun n -> kodkod_max_bound_ := Some n),
        " set upper cardinality bound for Kodkod"
      ; "--kodkod-bound-increment", Arg.Set_int kodkod_bound_increment_,
        " set cardinality bound increment for Kodkod"
      ; "--solvers", Arg.String set_solvers_,
        " solvers to use (comma-separated list) " ^ list_solvers_ ()
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
      ; "-d", Arg.Int Utils.set_debug, " alias to --debug"
      ]
  )

let pp_version_if_needed () =
  if !version_ then (
    Format.printf "nunchaku %s %s@." Const.version GitVersion.id;
    exit 0
  );
  ()

let parse_file ~into ~input () =
  let open E.Infix in
  let src = if !file = "" then `Stdin else `File !file in
  let rec by_input = function
    | I_guess ->
      begin match src with
        | `Stdin -> by_input I_nunchaku
        | `File f when CCString.suffix ~suf:".nun" f -> by_input I_nunchaku
        | `File f when CCString.suffix ~suf:".p" f -> by_input I_tptp
        | `File f when CCString.suffix ~suf:".smt2" f -> by_input I_tip
        | `File f -> raise (Arg.Bad ("cannot guess format of " ^ f))
      end
    | I_nunchaku ->
      Nunchaku_parsers.Lexer.parse ~into src
      >|= CCVector.freeze
    | I_tptp ->
      Nunchaku_parsers.TPTP_lexer.parse ~into ~mode:(`Env "TPTP") src
      >|= CCVector.to_seq
      >>= Nunchaku_parsers.TPTP_preprocess.preprocess
    | I_tip ->
      Nunchaku_parsers.Parse_tip.parse ~into src
      >|= CCVector.freeze
  in
  let res =
    try by_input input
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

let pp_input_if_needed statements =
  if !pp_ then
    Format.printf "@[<v2>input: {@,@[<v>%a@]@]@,}@."
      (Utils.pp_seq ~sep:"" A.pp_statement)
      (CCVector.to_seq statements);
  ()

module Pipes = struct
  module HO = TI.Default
  module Typed = TermTyped.Default
  (* type inference *)
  module Step_tyinfer = Tr.TypeInference.Make(Typed)(HO)
  module Step_conv_ty = Problem.Convert(Typed)(HO)
  (* conversion to FO *)
  module Step_tofo = Tr.Trans_ho_fo.Make(HO)
end

let close_task p =
  Transform.Pipe.close p
    ~f:(fun task ret ->
      Scheduling.Task.map ~f:ret task, CCFun.id)

(* get a file name prefix for "--dump", or [None] if "--dump" was not specified *)
let get_dump_file () = match !dump_ with
  | `No -> None
  | `Into dir ->
    let filename = match !file with
      | "" -> "nunchaku_problem"
      | f -> Filename.chop_extension (Filename.basename f) ^ ".nunchaku"
    in
    Some (Filename.concat dir filename)
  | `Yes ->
    begin match !file with
      | "" -> Some "nunchaku_problem"
      | f ->
        Some (Filename.chop_extension (Filename.basename f) ^ ".nunchaku")
    end

let make_cvc4 ~j () =
  let open Transform.Pipe in
  if List.mem S_CVC4 !solvers && Backends.CVC4.is_available ()
  then
    Backends.CVC4.pipes
      ~options:Backends.CVC4.options_l
      ~slice:(1. *. float j)
      ~dump:(get_dump_file ())
      ~print:!pp_all_
      ~schedule_options:!cvc4_schedule_
      ~print_smt:(!pp_all_ || !pp_smt_)
      ~print_model:(!pp_all_ || !pp_raw_model_)
      ()
    @@@ id
  else fail

let make_paradox () =
  let open Transform.Pipe in
  if List.mem S_paradox !solvers && Backends.Paradox.is_available ()
  then
    Backends.Paradox.pipe
      ~print_model:(!pp_all_ || !pp_raw_model_)
      ~dump:(get_dump_file ())
      ~print:!pp_all_ ()
    @@@ id
  else fail

let make_kodkod () =
  let open Transform.Pipe in
  if List.mem S_kodkod !solvers && Backends.Kodkod.is_available ()
  then
    Backends.Kodkod.pipe
      ~min_size:!kodkod_min_bound_
      ?max_size:!kodkod_max_bound_
      ~size_increment:!kodkod_bound_increment_
      ~print:!pp_all_
      ~dump:(get_dump_file ())
      ~print_model:(!pp_all_ || !pp_raw_model_)
      ()
    @@@ id
  else fail

let make_smbc () =
  let open Transform.Pipe in
  if List.mem S_smbc !solvers && Backends.Smbc.is_available ()
  then
    Backends.Smbc.pipe
      ~print:!pp_all_
      ~dump:(get_dump_file ())
      ~print_model:(!pp_all_ || !pp_raw_model_)
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
  let smbc = make_smbc () in
  let pipe_common k =
    Step_tyinfer.pipe ~print:(!pp_typed_ || !pp_all_) @@@
    Step_conv_ty.pipe () @@@
    Tr.Skolem.pipe
      ~skolems_in_model:!skolems_in_model_
      ~print:(!pp_skolem_ || !pp_all_) ~check ~mode:`Sk_types @@@
    k
  and pipe_mono_common k =
    Tr.Monomorphization.pipe
      ~always_mangle:false ~print:(!pp_mono_ || !pp_all_) ~check @@@
    Tr.Elim_infinite.pipe ~print:(!pp_elim_infinite || !pp_all_) ~check @@@
    Tr.ElimCopy.pipe ~print:(!pp_copy_ || !pp_all_) ~check @@@
    Tr.ElimMultipleEqns.pipe
      ~decode:(fun x->x) ~check
      ~print:(!pp_elim_multi_eqns || !pp_all_) @@@
    (if !enable_specialize_
     then Tr.Specialize.pipe ~print:(!pp_specialize_ || !pp_all_) ~check
     else Transform.nop ()) @@@
    Tr.Cstor_as_fun.pipe ~print:(!pp_cstor_as_fun_ || !pp_all_) ~check @@@
    k
  and pipe_common_paradox_kodkod k =
    Tr.ElimData.Codata.pipe ~print:(!pp_elim_codata_ || !pp_all_) ~check @@@
    (if !enable_polarize_
     then Tr.Polarize.pipe ~print:(!pp_polarize_ || !pp_all_)
         ~check ~polarize_rec:!polarize_rec_
     else Transform.nop ()) @@@
    Tr.Unroll.pipe ~print:(!pp_unroll_ || !pp_all_) ~check @@@
    Tr.Skolem.pipe
      ~skolems_in_model:!skolems_in_model_
      ~print:(!pp_skolem_ || !pp_all_) ~mode:`Sk_all ~check @@@
    Tr.ElimIndPreds.pipe ~print:(!pp_elim_preds_ || !pp_all_)
      ~check ~mode:`Use_selectors @@@
    Tr.ElimData.Data.pipe ~print:(!pp_elim_data_ || !pp_all_) ~check @@@
    Tr.LambdaLift.pipe ~print:(!pp_lambda_lift_ || !pp_all_) ~check @@@
    Tr.Elim_HOF.pipe ~print:(!pp_elim_hof_ || !pp_all_) ~check @@@
    Tr.ElimRecursion.pipe ~print:(!pp_elim_recursion_ || !pp_all_) ~check @@@
    Tr.IntroGuards.pipe ~print:(!pp_intro_guards_ || !pp_all_) ~check @@@
    Tr.Elim_prop_args.pipe ~print:(!pp_elim_prop_args_ || !pp_all_) ~check @@@
    k
  and pipe_paradox =
    Tr.ElimTypes.pipe ~print:(!pp_elim_types_ || !pp_all_) ~check @@@
    Tr.Model_clean.pipe ~print:(!pp_model_ || !pp_all_) @@@
    close_task (
      Step_tofo.pipe ~print:!pp_all_ () @@@
      Tr.Elim_ite.pipe ~print:(!pp_elim_ite_ || !pp_all_) @@@
      Tr.Trans_fo_tptp.pipe @@@
      paradox
    )
  and pipe_kodkod =
    Tr.Model_clean.pipe ~print:(!pp_model_ || !pp_all_) @@@
    close_task (
      Step_tofo.pipe ~print:!pp_all_ () @@@
      Tr.FoToRelational.pipe ~print:(!pp_fo_to_rel_ || !pp_all_) @@@
      kodkod
    )
  and pipe_smbc =
    Tr.Monomorphization.pipe
      ~always_mangle:true ~print:(!pp_mono_ || !pp_all_) ~check @@@
    Tr.Elim_infinite.pipe ~print:(!pp_elim_infinite || !pp_all_) ~check @@@
    Tr.ElimCopy.pipe ~print:(!pp_copy_ || !pp_all_) ~check @@@
    Tr.ElimMultipleEqns.pipe
      ~decode:(fun x->x) ~check
      ~print:(!pp_elim_multi_eqns || !pp_all_) @@@
    (if !enable_specialize_
     then Tr.Specialize.pipe ~print:(!pp_specialize_ || !pp_all_) ~check
     else Transform.nop ()) @@@
    (*
    Tr.Skolem.pipe
      ~skolems_in_model:!skolems_in_model_
      ~print:(!pp_skolem_ || !pp_all_) ~mode:`Sk_all ~check @@@
       *)
    Tr.ElimPatternMatch.pipe ~mode:Tr.ElimPatternMatch.Elim_codata_match
      ~print:(!pp_elim_codata_ || !pp_all_) ~check @@@
    Tr.Cstor_as_fun.pipe ~print:(!pp_cstor_as_fun_ || !pp_all_) ~check @@@
    Tr.ElimData.Codata.pipe ~print:(!pp_elim_codata_ || !pp_all_) ~check @@@
    (if !enable_polarize_
     then Tr.Polarize.pipe ~print:(!pp_polarize_ || !pp_all_)
         ~check ~polarize_rec:!polarize_rec_
     else Transform.nop ()) @@@
    Tr.Unroll.pipe ~print:(!pp_unroll_ || !pp_all_) ~check @@@
    (* skolemize first, to have proper decoding of model *)
    Tr.Skolem.pipe
      ~skolems_in_model:!skolems_in_model_
      ~print:(!pp_skolem_ || !pp_all_) ~mode:`Sk_all ~check @@@
    Tr.ElimIndPreds.pipe ~mode:`Use_match
      ~print:(!pp_elim_preds_ || !pp_all_) ~check @@@
    (*
    Tr.LambdaLift.pipe ~print:(!pp_lambda_lift_ || !pp_all_) ~check @@@
    Tr.Elim_HOF.pipe ~print:(!pp_elim_hof_ || !pp_all_) ~check @@@
       *)
    Tr.Lift_undefined.pipe ~print:!pp_all_ ~check @@@
    Tr.Model_clean.pipe ~print:(!pp_model_ || !pp_all_) @@@
    close_task smbc
  and pipe_cvc4 =
    (if !enable_polarize_
     then Tr.Polarize.pipe ~print:(!pp_polarize_ || !pp_all_)
         ~check ~polarize_rec:!polarize_rec_
     else Transform.nop ()) @@@
    Tr.Unroll.pipe ~print:(!pp_unroll_ || !pp_all_) ~check @@@
    Tr.Skolem.pipe
      ~skolems_in_model:!skolems_in_model_
      ~print:(!pp_skolem_ || !pp_all_) ~mode:`Sk_all ~check @@@
    Tr.ElimIndPreds.pipe
      ~mode:`Use_selectors
      ~print:(!pp_elim_preds_ || !pp_all_) ~check @@@
    Tr.LambdaLift.pipe ~print:(!pp_lambda_lift_ || !pp_all_) ~check @@@
    Tr.Elim_HOF.pipe ~print:(!pp_elim_hof_ || !pp_all_) ~check @@@
    Tr.ElimRecursion.pipe ~print:(!pp_elim_recursion_ || !pp_all_) ~check @@@
    Tr.IntroGuards.pipe ~print:(!pp_intro_guards_ || !pp_all_) ~check @@@
    Tr.Model_clean.pipe ~print:(!pp_model_ || !pp_all_) @@@
    close_task (
      Step_tofo.pipe ~print:!pp_all_ () @@@
      Transform.Pipe.flatten cvc4
    )
  in
  let pipe =
    pipe_common
      (fork
         pipe_smbc
         (pipe_mono_common @@
          Tr.ElimPatternMatch.pipe ~mode:Tr.ElimPatternMatch.Elim_both
            ~print:(!pp_elim_match_ || !pp_all_) ~check @@@
          fork
            (pipe_common_paradox_kodkod (fork pipe_paradox pipe_kodkod))
            pipe_cvc4))
  in
  pipe

let process_res_ r =
  let module Res = Problem.Res in
  (* [l] only contains unknown-like results (+timeout+out_of_scope),
     id recover accurate info *)
  let find_result_if_unknown l =
    let l =
      CCList.flat_map (function Res.Unknown l -> l | _ -> assert false) l
    in
    Res.Unknown l
  in
  match r with
    | Scheduling.Res_fail e -> E.fail (Printexc.to_string e)
    | Scheduling.Res_list [] -> E.fail "no task succeeded"
    | Scheduling.Res_list l ->
      assert
        (List.for_all
           (function
             | Res.Unknown _ -> true
             | Res.Error _ | Res.Sat _ | Res.Unsat _ -> false)
           l);
      let res = find_result_if_unknown l in
      E.return res
    | Scheduling.Res_one r -> E.return r

(* run the pipeline on this problem, then run tasks, and return the
   result *)
let run_tasks ~j ~deadline pipe pb =
  let module Res = Problem.Res in
  let tasks =
    Transform.run ~pipe pb
    |> Lazy_list.map ~f:(fun (task,ret) -> Scheduling.Task.map ~f:ret task)
    |> Lazy_list.to_list
  in
  match tasks with
    | [] -> E.return (Res.Unknown [])
    | _::_ ->
      let res = Scheduling.run ~j ~deadline tasks in
      process_res_ res

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
  (* check that there is something in the pipeline *)
  begin match pipe with
    | Transform.Pipe.Fail -> failwith "solvers are unavailable"
    | _ -> ()
  end;
  assert (not !pp_pipeline_);
  let deadline = Utils.Time.start () +. (float_of_int !timeout_) in
  run_tasks ~j:!j ~deadline pipe statements
  >|= fun res ->
  match res, output with
    | _, O_sexp ->
      let s = Problem.Res.to_sexp P.to_sexp P.to_sexp res in
      Format.printf "@[<hv2>%a@]@." Sexp_lib.pp s
    | Res.Sat (m,i), O_nunchaku when m.Model.potentially_spurious ->
      Format.printf "@[<v>@[<v2>SAT: (potentially spurious) {@,@[<v>%a@]@]@,}@,%a@]@."
        (Model.pp P.pp' P.pp) m Res.pp_info i;
    | Res.Sat (m,i), O_nunchaku ->
      Format.printf "@[<v>@[<v2>SAT: {@,@[<v>%a@]@]@,}@,%a@]@."
        Model.Default.pp_standard m Res.pp_info i;
    | Res.Sat (m,i), O_tptp ->
      (* XXX: if potentially spurious, what should we print? *)
      let module PM = Nunchaku_parsers.TPTP_print in
      Format.printf "@[<v2>%a@]@,%% %a@." PM.pp_model m Res.pp_info i
    | Res.Unsat i, O_nunchaku ->
      Format.printf "@[UNSAT@]@.%a@." Res.pp_info i
    | Res.Unsat i, O_tptp ->
      Format.printf "@[SZS Status: Unsatisfiable@]@.%% %a@." Res.pp_info i
    | Res.Unknown l, _ ->
      Format.printf "@[UNKNOWN@]@.(@[<hv>%a@])@." (Utils.pp_list Res.pp_unknown_info) l
    | Res.Error (e,_), _ ->
      raise e

(* main *)
let main () =
  let open E.Infix in
  CCFormat.set_color_default true; (* default: enable colors *)
  Arg.parse options set_file "usage: nunchaku [options] file";
  pp_version_if_needed ();
  if !pp_pipeline_ then (
    let pipe = make_model_pipeline() in
    Format.printf "@[Pipeline: %a@]@." Transform.Pipe.pp pipe;
    Transform.Pipe.check pipe;
    exit 0
  );
  (* parse *)
  parse_prelude (List.rev !prelude_)
  >>= fun statements ->
  parse_file ~into:statements ~input:!input_ ()
  >>= fun statements ->
  pp_input_if_needed statements;
  main_model ~output:!output_ statements

let () =
  E.catch (try main () with e -> Utils.err_of_exn e)
    ~ok:(fun () -> exit 0)
    ~err:(fun msg ->
      Format.eprintf "%s@." msg;
      exit 1
    )
