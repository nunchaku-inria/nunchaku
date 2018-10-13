
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Various Utils for Parsing} *)

open Nunchaku_core

module E = CCResult
module A = UntypedAST
module Loc = Location

type 'a or_error = ('a, string) CCResult.t

let section = Utils.Section.make "parser"

(** {2 Lexing} *)

exception LexError of Loc.t option * string
exception ParseError of Loc.t option * string

let () = Printexc.register_printer
    (function
      | LexError (loc, msg) ->
        Some (CCFormat.sprintf "@[<2>lexing error:@ %s@ at %a@]" msg Loc.pp_opt loc)
      | ParseError (loc,msg) ->
        Some (CCFormat.sprintf "@[<2>parsing error:@ %s@ at %a@]" msg Loc.pp_opt loc)
      | _ -> None
    )

let lex_error_ ?loc fmt =
  Utils.exn_ksprintf fmt ~f:(fun msg -> raise (LexError (loc, msg)))
let parse_error_ ?loc fmt =
  Utils.exn_ksprintf fmt ~f:(fun msg -> raise (ParseError (loc,msg)))

type statement = A.statement
type term = A.term
type ty = A.ty

(** {2 Parsing Shortcuts} *)

module type PARSER = sig
  type token
  val token : Lexing.lexbuf -> token

  type 'a parser_ = (Lexing.lexbuf -> token) -> Lexing.lexbuf -> 'a

  val parse_ty : ty parser_
  val parse_term : term parser_
  val parse_statement : statement parser_
  val parse_statement_list : statement list parser_
end

type include_mode =
  [ `None
  | `Relative
  | `Env of string (** Look in the given env variable for include path *)
  ]

module type S = sig
  val parse :
    ?mode:include_mode ->
    ?into:statement CCVector.vector ->
    [`File of string | `Stdin] ->
    statement CCVector.vector or_error

  val ty_of_string : string -> ty or_error

  val ty_of_string_exn : string -> ty

  val term_of_string : string -> term or_error

  val term_of_string_exn : string -> term

  val statement_of_string : string -> statement or_error

  val statement_of_string_exn : string -> statement
end

let error_include_ ?loc f =
  parse_error_ ?loc "@[<2>include not found:@ `%s`@]" f

(* try the list of files, parse the first existing one.
   @param p the parser to use to parse the file *)
let rec try_files ?loc ~p f l = match l with
  | [] -> error_include_ ?loc f
  | f' :: _ when Sys.file_exists f' -> p f'
  | _ :: l' -> try_files ?loc ~p f l'

module Make(P : PARSER) : S = struct
  include P

  let rec parse_buf_rec ?loc ~mode ~basedir ~res lexbuf =
    let l = P.parse_statement_list P.token lexbuf in
    let rel_include f = Filename.concat basedir (Filename.basename f) in
    List.iter
      (fun st -> match st.A.stmt_value with
         | A.Include (f, _which) ->
           (* TODO: handle partial includes *)
           (* include file *)
           let files = match mode with
             | `None -> [f]
             | `Relative ->
               [f; rel_include f]
             | `Env envvar ->
               try
                 let dir = Sys.getenv envvar in
                 [f; rel_include f; Filename.concat dir f]
               with Not_found ->
                 Utils.debugf ~section 1
                   "@[could not find environment variable `%s`@ while trying to include `%s`@]"
                   (fun k->k f envvar);
                 [f; rel_include f]
           in
           try_files ?loc f files
             ~p:(fun f ->
               parse_rec ~loc:st.A.stmt_loc ~mode ~basedir ~res (`File f))
         | _ ->
           (* simply keep the statement *)
           CCVector.push res st)
      l

  and parse_rec ?loc ~mode ~basedir ~res (src : [`Stdin | `File of string]) =
    match src with
      | `Stdin ->
        let lexbuf = Lexing.from_channel stdin in
        Loc.set_file lexbuf "<stdin>"; (* for error reporting *)
        parse_buf_rec ?loc ~mode ~res ~basedir lexbuf
      | `File f ->
        CCIO.with_in f
          (fun ic ->
             let lexbuf = Lexing.from_channel ic in
             Loc.set_file lexbuf f;
             parse_buf_rec ?loc ~mode ~basedir ~res lexbuf)

  let parse ?(mode=`Relative) ?into:(res=CCVector.create()) src =
    let basedir = match src with
      | `File f -> Filename.dirname f
      | `Stdin -> "."
    in
    try
      parse_rec ~mode ~res ~basedir src;
      E.return res
    with e ->
      E.fail (Printexc.to_string e)

  let parse_str_ p s = p P.token (Lexing.from_string s)

  let try_parse_ p s =
    try E.return (parse_str_ p s)
    with e -> E.fail (Printexc.to_string e)

  let ty_of_string = try_parse_ P.parse_ty
  let ty_of_string_exn = parse_str_ P.parse_ty

  let term_of_string = try_parse_ P.parse_term
  let term_of_string_exn = parse_str_ P.parse_term

  let statement_of_string = try_parse_ P.parse_statement
  let statement_of_string_exn = parse_str_ P.parse_statement
end
