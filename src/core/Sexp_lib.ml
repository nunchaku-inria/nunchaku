
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Simple and efficient S-expression parsing/printing}

    Windows-aware printer and parser, using ocamllex/ocamlyacc *)

type 'a or_error = [ `Ok of 'a | `Error of string ]
type 'a sequence = ('a -> unit) -> unit
type 'a gen = unit -> 'a option

type t = [
  | `Atom of string
  | `List of t list
]
type sexp = t

let atom s = `Atom s
let list l = `List l

(* shall we escape the string because of one of its chars? *)
let _must_escape s =
  try
    for i = 0 to String.length s - 1 do
      let c = String.unsafe_get s i in
      match c with
        | ' ' | ';' | ')' | '(' | '"' | '\\' | '\n' | '\t' -> raise Exit
        | _ when Char.code c > 127 -> raise Exit  (* non-ascii *)
        | _ -> ()
    done;
    false
  with Exit -> true

let rec pp out t = match t with
  | `Atom s when _must_escape s -> Format.fprintf out "\"%s\"" (String.escaped s)
  | `Atom s -> Format.pp_print_string out s
  | `List [] -> Format.pp_print_string out "()"
  | `List [x] -> Format.fprintf out "@[<hov2>(%a)@]" pp x
  | `List l ->
    Format.fprintf out "@[<hov1>(";
    List.iteri
      (fun i t' -> (if i > 0 then Format.fprintf out "@ "; pp out t'))
      l;
    Format.fprintf out ")@]"

let to_string = CCFormat.to_string pp

let pp_newline out () =
  if Sys.cygwin||Sys.win32
  then CCFormat.string out "\r\n"
  else CCFormat.char out '\n'

let to_chan oc t =
  let out = Format.formatter_of_out_channel oc in
  pp out t;
  pp_newline out ();
  Format.pp_print_flush out ()

let to_file filename s =
  CCIO.with_out filename
    (fun oc -> to_chan oc s)

type 'a parse_result = ['a or_error | `End ]
(** A parser of ['a] can return [`Ok x] when it parsed a value,
    or [`Error e] when a parse error was encountered, or
    [`End] if the input was empty *)

module Decoder = struct
  module L = Sexp_lex

  type t = {
    buf: Lexing.lexbuf;
    mutable cur_tok: L.token option; (* current token *)
  }

  let cur (t:t): L.token = match t.cur_tok with
    | Some L.EOI -> assert false
    | Some t -> t
    | None ->
      (* fetch token *)
      let tok = L.token t.buf in
      t.cur_tok <- Some tok;
      tok

  let junk t = t.cur_tok <- None

  let of_lexbuf buf = {
    buf;
    cur_tok=None;
  }

  exception E_end
  exception E_error of string

  let next (t:t) =
    let rec expr () = match cur t with
      | L.EOI -> raise E_end
      | L.ATOM s -> junk t; `Atom s
      | L.LIST_OPEN ->
        junk t;
        let l = lst [] in
        begin match cur t with
          | L.LIST_CLOSE -> junk t; `List l
          | _ -> raise (E_error "expected ')'")
        end
      | L.LIST_CLOSE -> raise (E_error "expected expression")
    and lst acc = match cur t with
      | L.LIST_CLOSE -> List.rev acc
      | L.LIST_OPEN | L.ATOM _ ->
        let sub = expr () in
        lst (sub::acc)
      | L.EOI -> raise (E_error "unexpected EOI")
    in
    try `Ok (expr ())
    with
      | E_end -> `End
      | E_error msg ->
        let loc = Location.of_lexbuf t.buf in
        `Error (CCFormat.sprintf "parse error at %a: %s" Location.print loc msg)
end

let parse_string s : t or_error =
  let buf = Lexing.from_string s in
  let d = Decoder.of_lexbuf buf in
  match Decoder.next d with
    | `End -> `Error "unexpected end of file"
    | (`Ok _ | `Error _) as res -> res

(*$T
  CCError.to_opt (parse_string "(abc d/e/f \"hello \\\" () world\" )") <> None
  CCError.to_opt (parse_string "(abc ( d e ffff   ) \"hello/world\")") <> None
*)

(*$inject
  let sexp_gen =
    let mkatom a = `Atom a and mklist l = `List l in
    let atom = Q.Gen.(map mkatom (string_size ~gen:printable (1 -- 30))) in
    let gen = Q.Gen.(
      sized (fix
        (fun self n st -> match n with
        | 0 -> atom st
        | _ ->
          frequency
            [ 1, atom
            ; 2, map mklist (list_size (0 -- 10) (self (n/10)))
            ] st
        )
    )) in
    let rec small = function
      | `Atom s -> String.length s
      |  `List l -> List.fold_left (fun n x->n+small x) 0 l
    and print = function
      | `Atom s -> Printf.sprintf "`Atom \"%s\"" s
      | `List l -> "`List " ^ Q.Print.list print l
    and shrink = function
      | `Atom s -> Q.Iter.map mkatom (Q.Shrink.string s)
      | `List l -> Q.Iter.map mklist (Q.Shrink.list ~shrink l)
    in
    Q.make ~print ~small ~shrink gen

  let rec sexp_valid  = function
    | `Atom "" -> false
    | `Atom _ -> true
    | `List l -> List.for_all sexp_valid l
*)

(*$Q & ~count:100
    sexp_gen (fun s -> sexp_valid s ==> (to_string s |> parse_string = `Ok s))
*)

let parse_chan ic =
  let buf = Lexing.from_channel ic in
  let d = Decoder.of_lexbuf buf in
  match Decoder.next d with
    | `End -> `Error "unexpected end of file"
    | (`Ok _ | `Error _) as res -> res

let parse_chan_list ic =
  let buf = Lexing.from_channel ic in
  let d = Decoder.of_lexbuf buf in
  let rec iter acc = match Decoder.next d with
    | `End -> `Ok (List.rev acc)
    | `Ok x -> iter (x::acc)
    | `Error _ as e -> e
  in
  iter []

let parse_file filename = CCIO.with_in filename parse_chan

let parse_file_list filename = CCIO.with_in filename parse_chan_list
