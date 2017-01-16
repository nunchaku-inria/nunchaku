
(* This file is free software, part of nunchaku. See file "license" for more details. *)

module A = UntypedAST

let choice = ID.make "choice"
let unique = ID.make "unique"
let unique_unsafe = ID.make "unique_unsafe"

exception Parse_error of string

let () = Printexc.register_printer
    (function
      | Parse_error msg -> Some msg
      | _ -> None)

let parse_error_ msg = raise (Parse_error msg)
let parse_errorf_ msg = CCFormat.ksprintf ~f:parse_error_ msg

let loc = Location.mk "<prelude>" 0 0 0 0

(* parser for a very simple S-expr based language *)
let sexp_to_term : Sexp_lib.t -> A.term =
  let rec p = function
    | `List (`Atom "asserting" :: t :: l) -> A.asserting ~loc (p t) (List.map p l)
    | `List [`Atom "=>"; a; b] -> A.imply ~loc (p a) (p b)
    | `List [`Atom "="; a; b] -> A.eq ~loc (p a) (p b)
    | `List [`Atom "!="; a; b] -> A.neq ~loc (p a) (p b)
    | `List [`Atom "<=>"; a; b] -> A.equiv ~loc (p a) (p b)
    | `List (`Atom "and" :: l) -> A.and_ ~loc (List.map p l)
    | `List (`Atom "or" :: l) -> A.or_ ~loc (List.map p l)
    | `List [`Atom "not"; t] -> A.not_ ~loc (p t)
    | `List [`Atom "->"; a; b] -> A.ty_arrow ~loc (p a) (p b)
    | `List [`Atom "forall"; `Atom v; t] -> A.forall ~loc (v, None) (p t)
    | `List [`Atom "forall"; `Atom v; ty; t] -> A.forall ~loc (v, Some (p ty)) (p t)
    | `List [`Atom "exists"; `Atom v; t] -> A.exists ~loc (v, None) (p t)
    | `List [`Atom "exists"; `Atom v; ty; t] -> A.exists ~loc (v, Some (p ty)) (p t)
    | `List [`Atom "pi"; `Atom v; t] -> A.ty_forall ~loc v (p t)
    | `List [`Atom "fun"; `Atom v; t] -> A.fun_ ~loc (v,None) (p t)
    | `List [`Atom "fun"; `Atom v; ty; t] -> A.fun_ ~loc (v,Some (p ty)) (p t)
    | `Atom "prop" -> A.ty_prop
    | `Atom "type" -> A.ty_type
    | `Atom "true" -> A.true_
    | `Atom "false" -> A.false_
    | `Atom v -> A.var ~loc v
    | `List (`Atom v :: l) -> A.app ~loc (A.var ~loc v) (List.map p l)
    | s -> parse_errorf_ "@[<2>expected term, got @[%a@]@]" Sexp_lib.pp s
  in
  p

let p_term s =
  match Sexp_lib.parse_string s with
    | `Ok s -> sexp_to_term s
    | `Error msg ->
      parse_errorf_ "could not parse `%s` as an S-expression: %s" s msg


(* the type: [pi a. (a -> prop) -> a] *)
let ty_choice_ = p_term "(pi a (-> (-> a prop) a))"

let mk_stmt d =
  { A.
    stmt_loc=Some loc;
    stmt_name=None;
    stmt_value=d;
  }

let decl_choice =
  let ax = p_term
      "(forall p
       (=
        (choice p)
        (asserting
          (choice p)
          (or (= p (fun x false))
              (p (choice p)))))))"
  in
  A.Rec [ ID.name choice, ty_choice_, [ax] ] |> mk_stmt

let decl_unique =
  let ax = p_term
      "(forall p
       (=
        (unique p)
        (asserting
         (unique p)
         (or
           (= p (fun x (= x (unique p))))
           (= p (fun x false))
           (exists x (exists y (and (!= x y) (p x) (p y)))))))))"
  in
  A.Rec [ ID.name unique, ty_choice_, [ax] ] |> mk_stmt

let decl_unique_unsafe =
  let ax = p_term
      "(forall p
       (=
        (unique_unsafe p)
        (asserting
         (unique_unsafe p)
         (p (unique_unsafe p)))))"
  in
  A.Rec [ ID.name unique_unsafe, ty_choice_, [ax] ] |> mk_stmt

let decls =
  [ decl_choice
  ; decl_unique
  ; decl_unique_unsafe
  ]


