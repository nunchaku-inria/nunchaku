
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Lazy List} *)

type +'a t = 'a cell lazy_t
and +'a cell =
  | Nil
  | Cons of 'a * 'a t

let empty = Lazy.from_val Nil

let return x = Lazy.from_val (Cons (x, empty))

let is_empty = function
  | lazy Nil -> true
  | lazy (Cons _) -> false

let cons x tl = Lazy.from_val (Cons (x,tl))

let head = function
  | lazy Nil -> None
  | lazy (Cons (x, tl)) -> Some (x,tl)

let rec map ~f l =
  lazy (
    match l with
      | lazy Nil -> Nil
      | lazy (Cons (x,tl)) -> Cons (f x, map ~f tl)
  )

let rec append a b =
  lazy (
    match a with
      | lazy Nil -> Lazy.force b
      | lazy (Cons (x,tl)) -> Cons (x, append tl b)
  )

let rec flat_map ~f l =
  lazy (
    match l with
      | lazy Nil -> Nil
      | lazy (Cons (x,tl)) ->
        let res = append (f x) (flat_map ~f tl) in
        Lazy.force res
  )

module Infix = struct
  let (>|=) x f = map ~f x
  let (>>=) x f = flat_map ~f x
end

include Infix

type 'a gen = unit -> 'a option

let rec of_gen g =
  lazy (
    match g()  with
      | None -> Nil
      | Some x -> Cons (x, of_gen g)
  )

let rec of_list = function
  | [] -> empty
  | x :: tl -> cons x (of_list tl)

let to_list_rev l =
  let rec aux acc = function
    | lazy Nil -> acc
    | lazy (Cons (x,tl)) -> aux (x::acc) tl
  in
  aux [] l

let to_list l = to_list_rev l |> List.rev
