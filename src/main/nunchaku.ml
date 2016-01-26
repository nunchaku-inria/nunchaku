
(** {1 Main program} *)

open Nunchaku_core

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

(** {2 Options} *)

let input_ = ref I_nunchaku
let output_ = ref O_nunchaku
let polarize_rec_ = ref true
let print_ = ref false
let print_all_ = ref false
let print_pipeline_ = ref false
let print_typed_ = ref false
let print_skolem_ = ref false
let print_mono_ = ref false
let print_elim_match_ = ref false
let print_recursion_elim_ = ref false
let print_elim_multi_eqns = ref false
let print_polarize_ = ref false
let print_unroll_ = ref false
let print_elim_preds_ = ref false
let print_copy_ = ref false
let print_intro_guards_ = ref false
let print_fo_ = ref false
let print_smt_ = ref false
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

let options =
  let open CCFun in
  Arg.align ?limit:None @@ List.sort Pervasives.compare @@ (
  options_debug_ @
  Utils.options_warnings_ @
  [ "--print-input", Arg.Set print_, " print input"
  ; "--print-all", Arg.Set print_all_, " print every step of the pipeline"
  ; "--print-pipeline", Arg.Set print_pipeline_, " print full pipeline"
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
      , Arg.Set print_recursion_elim_
      , " print input after elimination of recursive functions"
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
  ; "--print-raw-model", Arg.Set Solver_intf.print_model_, " print raw model"
  ; "--print-model", Arg.Set print_model_, " print model after cleanup"
  ; "--color", Arg.Bool CCFormat.set_color_default, " enable/disable color"
  ; "-j", Arg.Set_int j, " set parallelism level"
  ; "--polarize-rec", Arg.Set polarize_rec_, " enable polarization of rec predicates"
  ; "--no-polarize-rec", Arg.Clear polarize_rec_, " disable polarization of rec predicates"
  ; "--no-polarize", Arg.Clear enable_polarize_, " disable polarization"
  ; "--timeout", Arg.Set_int timeout_, " set timeout (in s)"
  ; "--input", Arg.String set_input_, " set input format " ^ list_inputs_ ()
  ; "--output", Arg.String set_output_, " set output format " ^ list_outputs_ ()
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
  module Step_elim_preds = ElimIndPreds.Make(HO)
  module Step_rec_elim = ElimRecursion.Make(HO)
  module Step_polarize = Polarize.Make(HO)
  module Step_unroll = Unroll.Make(HO)
  module Step_elim_copy = ElimCopy.Make(HO)
  module Step_intro_guards = IntroGuards.Make(HO)
  (* conversion to FO *)
  module Step_tofo = TermMono.TransFO(HO)(FO.Default)
  (* renaming in model *)
  module Step_rename_model = Model.Util(HO)
end

(* build a pipeline, depending on options *)
let make_model_pipeline () =
  let open Transform.Pipe in
  let open Pipes in
  (* setup pipeline *)
  let pipe =
    Step_tyinfer.pipe ~print:(!print_typed_ || !print_all_) @@@
    Step_conv_ty.pipe () @@@
    Step_skolem.pipe ~print:(!print_skolem_ || !print_all_) ~mode:`Sk_types @@@
    Step_mono.pipe ~print:(!print_mono_ || !print_all_) @@@
    Step_ElimMultipleEqns.pipe
      ~decode:(fun x->x)
      ~print:(!print_elim_multi_eqns || !print_all_) @@@
    (if !enable_polarize_
      then Step_polarize.pipe ~print:(!print_polarize_ || !print_all_)
        ~polarize_rec:!polarize_rec_
      else Transform.nop ())
    @@@
    Step_unroll.pipe ~print:(!print_unroll_ || !print_all_) @@@
    Step_skolem.pipe ~print:(!print_skolem_ || !print_all_) ~mode:`Sk_all @@@
    Step_elim_preds.pipe ~print:(!print_elim_preds_ || !print_all_) @@@
    Step_rec_elim.pipe ~print:(!print_recursion_elim_ || !print_all_) @@@
    Step_ElimMatch.pipe ~print:(!print_elim_match_ || !print_all_) @@@
    Step_elim_copy.pipe ~print:(!print_copy_ || !print_all_) @@@
    Step_intro_guards.pipe ~print:(!print_intro_guards_ || !print_all_) @@@
    Step_rename_model.pipe_rename ~print:(!print_model_ || !print_all_) @@@
    Step_tofo.pipe () @@@
    id
  in
  let deadline = Utils.Time.start () +. (float_of_int !timeout_) in
  CVC4.close_pipe FO.default ~options:CVC4.options_l ~j:!j
    ~pipe ~deadline
      ~print:(!print_fo_ || !print_all_)
      ~print_smt:(!print_smt_ || !print_all_)

(* search for results *)
let rec find_model_ ~found_unsat l =
  let module Res = Problem.Res in
  try
  match l() with
    | `Nil ->
        E.return (if found_unsat then `Unsat else `Unknown)
    | `Cons ((res, conv_back), tail) ->
        match res with
        | Res.Timeout -> E.return `Timeout
        | Res.Unknown -> find_model_ ~found_unsat tail
        | Res.Unsat -> find_model_ ~found_unsat:true tail
        | Res.Sat m ->
            let m = conv_back m in
            E.return (`Sat m)
  with e -> Utils.err_of_exn e

(* negate the goal *)
let negate_goal stmts =
  let module A = UntypedAST in
  CCVector.map
    (fun st -> match st.A.stmt_value with
      | A.Goal f -> {st with A.stmt_value=A.Goal (A.not_ f); }
      | _ -> st
    ) stmts

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
  Transform.run_closed ~cpipe statements |> find_model_ ~found_unsat:false
  >|= fun res ->
  begin match res, output with
  | `Sat m, O_nunchaku when m.Model.potentially_spurious ->
      Format.printf "@[<v>@[<v2>SAT: (potentially spurious) {@,@[<v>%a@]@]@,}@]@."
        (Model.print UntypedAST.print_term UntypedAST.print_term) m;
  | `Sat m, O_nunchaku ->
      Format.printf "@[<v>@[<v2>SAT: {@,@[<v>%a@]@]@,}@]@."
        (Model.print UntypedAST.print_term UntypedAST.print_term) m;
  | `Sat m, O_tptp ->
      (* XXX: if potentially spurious, what should we print? *)
      Format.printf "@[<v2>%a@]@,@." NunPrintTPTP.print_model m
  | `Unsat, O_nunchaku ->
      Format.printf "@[UNSAT@]@."
  | `Unsat, O_tptp ->
      Format.printf "@[SZS Status: Unsatisfiable@]@."
  | `Unknown, _ ->
      Format.printf "@[UNKNOWN@]@."
  | `Timeout, _ ->
      Format.printf "@[TIMEOUT@]@."
  end;
  ()

(* main *)
let main () =
  CCFormat.set_color_default true; (* default: enable colors *)
  Arg.parse options set_file "usage: nunchaku [options] file";
  print_version_if_needed ();
  (* parse *)
  parse_file ~input:!input_ ()
  >>= fun statements ->
  print_input_if_needed statements;
  main_model ~output:!output_ statements

let () =
  E.catch (main ())
  ~ok:(fun () -> exit 0)
  ~err:(fun msg ->
    Format.eprintf "%s@." msg;
    exit 1
  )
