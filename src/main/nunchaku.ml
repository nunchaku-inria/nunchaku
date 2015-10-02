
(** {1 Main program} *)

module E = CCError
module A = NunUntypedAST
module Utils = NunUtils

(** {2 Type Inference} *)

module T = NunTerm_typed

(* type inference *)
module Conv = NunTypeInference.ConvertStatement(struct
  include NunStatement_loc
  module T = T
end)

module PrintT = NunTerm_intf.Print(T)
module PrintTy = NunType_intf.Print(T.Ty)

let print_statement = NunStatement_loc.print PrintT.print PrintTy.print
let print_statement_list = NunStatement_loc.print_list PrintT.print PrintTy.print

(** {2 Options} *)

let print_ = ref false
let print_typed_ = ref false
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
  ; "--print-typed", Arg.Set print_typed_, " print input after typing and exit"
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

let print_typed_if_needed statements =
  if !print_typed_ then (
    Format.printf "@[%a@]@." print_statement_list statements;
    exit 0
  );
  ()

(* main *)
let main () =
  let open CCError.Infix in
  Arg.parse options set_file "usage: nunchaku [options] file";
  print_version_if_needed ();
  parse_file ()
  >>= fun statements ->
  print_input_if_needed statements;
  Conv.convert_list ~env:Conv.empty_env statements
  >>= fun (statements, _) ->
  print_typed_if_needed statements;
  Utils.not_implemented "main translation"

let () =
  E.catch (main ())
    ~ok:(fun () -> exit 0)
    ~err:(fun msg ->
      Format.eprintf "%s@." msg;
      exit 1
    )
