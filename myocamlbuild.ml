(* OASIS_START *)
(* OASIS_STOP *)

open Ocamlbuild_plugin;;

let bracket res destroy k =
  let x = try k res with e -> destroy res; raise e in
  destroy res;
  x

let cmd cmd =
  bracket
    (Unix.open_process_in cmd)
    (fun ch -> ignore & Unix.close_process_in ch)
    input_line

let git_describe () =
  try
    let id = cmd "git rev-parse HEAD" in
    Printf.sprintf "let id = \"(commit %s)\"" id
  with _ -> "let id = \"\""

let doc_intro = "doc/intro.txt";;

let qtest_preamble = "open Nunchaku_core;; "

let import_qtestpack build packfile =
  let tags1 = tags_of_pathname packfile in
  let files = string_list_of_file packfile in
  let include_dirs = Pathname.include_dirs_of (Pathname.dirname packfile) in
  let files_alternatives =
    List.map begin fun module_name ->
      expand_module include_dirs module_name ["ml"; "mli"]
    end files
  in
  let files = List.map Outcome.good (build files_alternatives) in
  let tags2 =
    List.fold_right
      (fun file -> Tags.union (tags_of_pathname file))
      files tags1
  in
  (tags2, files)

let qtest_many target packfile env build =
  let packfile = env packfile and target = env target in
  let tags, files = import_qtestpack build packfile in
  Cmd(S[A "qtest";
        A "extract"; A "--preamble"; A qtest_preamble; T tags;
        A "-o"; A target; Command.atomize_paths files]);;

dispatch
  (MyOCamlbuildBase.dispatch_combine [
    begin function
    | After_rules ->
      (* Documentation index *)
      dep ["ocaml"; "doc"; "extension:html"] & [doc_intro] ;
      flag ["ocaml"; "doc"; "extension:html"]
        & S[A"-t"; A"Nunchaku documentation"; A"-intro"; P doc_intro ];
      rule "git version" ~prod:"%GitVersion.ml"
        (fun env _ ->
          let v = git_describe() in
          let out = env "%GitVersion.ml" in
          Cmd (S [A "echo"; Quote (Sh v); Sh ">"; Px out]));

      rule "ocaml: modular qtest (qtestpack)"
        ~prods:["%.ml"]
        ~deps:["%.qtestpack"]
        ~doc:"Qtest supports building a test module by extracting cases
              directly from several composing several .ml{,i} files together.  \
              To use that feature with ocamlbuild, you should create a .qtestpack \
              file with the same syntax as .mllib or .mlpack files: \
              a whitespace-separated list of the capitalized module names \
              of the .ml{,i} files you want to combine together."
        (qtest_many "%.ml" "%.qtestpack");

    | _ -> ()
    end;
    dispatch_default
    ])
