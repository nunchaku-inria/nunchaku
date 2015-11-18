
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Constant} *)

module ID = NunID

type id = NunID.t

type 'term t = {
  id: id; (* symbol *)
  ty: 'term; (* type of symbol *)
  mutable def: 'term def; (* definition/declaration for the symbol *)
}
and 'term def =
  | Cstor of
      'term (* the datatype *)
      * 'term t list (* list of all constructors *)

  | Def of 'term (* id == this term *)

  | Overload of
      ('term * 'term def) list
      (* decision tree based on the first (type) argument:
        each [arg,def'] in the list means that [id arg = def'] *)

  | Datatype of
      [`Data | `Codata]
      * 'term t list (* list of constructors *)

  | Opaque

let is_cstor c = match c.def with Cstor _ -> true | _ -> false
let is_def c = match c.def with (Overload _ | Def _) -> true | _ -> false

let make ~def ~ty id = {def; ty; id}

exception Invalid of string

let invalid_ msg = raise (Invalid msg)
let invalidf_ msg = NunUtils.exn_ksprintf msg ~f:invalid_

let add_def c ~args t =
  let rec aux def args t = match def, args with
    | Opaque, [] -> Def t
    | Opaque, a :: args' ->
        Overload [a, aux Opaque args' t]
    | Overload _, [] ->
        invalidf_
          "%a: overloaded definition of incompatible arity" ID.print_name c.id
    | Overload cases, a :: args' ->
        Overload ((a, aux Opaque args' t) :: cases)
    | Def _, _ ->
        invalidf_ "%a is already defined, cannot redefine it" ID.print_name c.id
    | Cstor _, _ ->
        invalidf_ "%a is a constructor, cannot define it" ID.print_name c.id
    | Datatype _, _ ->
        invalidf_ "%a is a datatype, cannot define it" ID.print_name c.id
  in
  c.def <- aux c.def args t


