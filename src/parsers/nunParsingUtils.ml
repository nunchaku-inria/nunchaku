
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Various Utils for Parsing} *)

module E = CCError
module A = NunUntypedAST
module Loc = NunLocation

type 'a or_error = [`Ok of 'a | `Error of string ]

(** {2 Lexing} *)

exception LexError of string

let () = Printexc.register_printer
  (function
    | LexError msg -> Some ("lexing error: " ^ msg)
    | _ -> None
  )

let lex_error_ fmt =
  NunUtils.exn_ksprintf ~f:(fun msg -> raise (LexError msg)) fmt

type statement = A.statement
type term = A.term
type ty = A.ty

(** {2 Parsing Shortcuts} *)

module type FORMAT = sig
  type token
  val token : Lexing.lexbuf -> token

  type 'a parser_ = (Lexing.lexbuf -> token) -> Lexing.lexbuf -> 'a

  val parse_ty : ty parser_
  val parse_term : term parser_
  val parse_statement : statement parser_
  val parse_statement_list : statement list parser_
end

module Make(F : FORMAT) = struct

  let parse_file file =
    try
      CCIO.with_in file
        (fun ic ->
          let lexbuf = Lexing.from_channel ic in
          Loc.set_file lexbuf file; (* for error reporting *)
          E.return (F.parse_statement_list F.token lexbuf)
        )
    with e ->
      E.fail (Printexc.to_string e)

  let parse_stdin () =
    try
      let lexbuf = Lexing.from_channel stdin in
      Loc.set_file lexbuf "<stdin>"; (* for error reporting *)
      E.return (F.parse_statement_list F.token lexbuf)
    with e ->
      E.fail (Printexc.to_string e)

  let parse_str_ p s = p F.token (Lexing.from_string s)

  let try_parse_ p s =
    try E.return (parse_str_ p s)
    with e -> E.fail (Printexc.to_string e)

  let ty_of_string = try_parse_ F.parse_ty
  let ty_of_string_exn = parse_str_ F.parse_ty

  let term_of_string = try_parse_ F.parse_term
  let term_of_string_exn = parse_str_ F.parse_term

  let statement_of_string = try_parse_ F.parse_statement
  let statement_of_string_exn = parse_str_ F.parse_statement

  module HO = struct
    module T = NunTerm_ho.Default
    module Conv = NunTerm_ho.OfUntyped(T)

    let term_of_str_exn s =
      let t = term_of_string_exn s in
      Conv.convert_term t

    let term_of_str s =
      try CCError.return (term_of_str_exn s)
      with e -> NunUtils.err_of_exn e
  end
end
