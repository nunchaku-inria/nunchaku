
(** {1 Main program} *)

module E = CCError
module A = NunAST
module Utils = NunUtils

(** {2 Options} *)

let print_ = ref false
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
  ]
)

(* main *)
let main () =
  let open CCError.Infix in
  Arg.parse options set_file "usage: nunchaku [options] file";
  ( if !file = "" then (
      Utils.debugf 1 "will read on stdin";
      NunLexer.parse_stdin ()
    ) else NunLexer.parse_file !file
  )
  >>= fun statements ->
  if !print_ then (
    Format.printf "@[%a@]@." A.print_statement_list statements;
    E.return ()
  ) else Utils.not_implemented "main translation"

let () =
  E.catch (main ())
    ~ok:(fun () -> exit 0)
    ~err:(fun msg ->
      Utils.debugf 0 "%s" msg;
      exit 1
    )
