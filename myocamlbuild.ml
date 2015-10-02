(* OASIS_START *)
(* OASIS_STOP *)

open Ocamlbuild_plugin;;

let doc_intro = "doc/intro.txt";;

dispatch
  (MyOCamlbuildBase.dispatch_combine [
    begin function
    | After_rules ->
      (* Documentation index *)
      dep ["ocaml"; "doc"; "extension:html"] & [doc_intro] ;
      flag ["ocaml"; "doc"; "extension:html"]
        & S[A"-t"; A"Containers doc"; A"-intro"; P doc_intro ];
    | _ -> ()
    end;
    dispatch_default
  ])
