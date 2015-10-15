#!/usr/bin/env ocaml

(* run tests *)

#use "topfind";;
#require "gen";;
#require "containers";;
#require "containers.string";;
#require "containers.unix";;

type result =
  | Ok
  | Error (* should fail *)

let pp_result out e =
  Format.fprintf out "%s"
    (match e with Ok -> "ok" | Error -> "error")

(* what is expected? *)
let grep_expect f =
  CCIO.with_in f
    (fun ic ->
      let g = CCIO.read_lines ic
        |> Gen.map String.trim
        |> Gen.map String.lowercase
        |> Gen.filter_map
          (function
            | "# expect: ok" -> Some Ok
            | "# expect: error"
            | "# expect: fail" -> Some Error
            | _ -> None
          )
      in
      match g() with
      | None -> failwith ("cannot read expected result for " ^ f)
      | Some r -> r
    )

(* run test for [f] , and return [true] if test was ok *)
let test_file f =
  Format.printf "running %-30s... @?" f;
  (* expected result *)
  let expected = grep_expect f in
  let p = CCUnix.call "./nunchaku.native --timeout 5 %s" f in
  let actual = if p#errcode = 0 then Ok else Error in
  if expected = actual
  then (Format.printf "\x1b[32;1mok\x1b[0m@."; true)
  else (
    Format.printf "\x1b[31;1mfailure\x1b[0m: expected `%a`, got `%a`@."
      pp_result expected pp_result actual;
    false
  )

(* find list of files to test *)
let gather_files () =
  CCIO.File.read_dir ~recurse:true "tests"
  |> Gen.filter (CCString.suffix ~suf:".nun")
  |> Gen.to_rev_list

let () =
  Arg.parse [] (fun _ -> failwith "no arguments") "./tests/run.ml";
  Format.printf "run tests@.";
  let files = gather_files () in
  let num_failed = List.fold_left
    (fun acc f ->
      let ok = test_file f in
      (if ok then 0 else 1) + acc
    )
    0 files
  in
  if num_failed = 0 then ()
  else (
    Format.printf "%d test(s) failed@." num_failed;
    exit 1
  )

