
(* This file is free software, part of containers. See file "license" for more details. *)

type t = {
  name: string;
  mutable id: int;
}
(** A symbol. Two symbols for the same name are physically equal *)

type sym = t

(* Weak table for interning strings *)
module W = Weak.Make(struct
  type t = sym
  let equal a b = a.name = b.name
  let hash a = Hashtbl.hash a.name
end)

let make =
  let tbl = W.create 256 in
  let n = ref 0 in (* unique ID generator *)
  fun name ->
    let s = {name; id= ~-1; } in
    let s' = W.merge tbl s in
    if s == s' then (
      (* new symbol *)
      s'.id <- !n;
      incr n;
    );
    s'

let equal a b = a.id = b.id
let compare a b = Pervasives.compare a.id b.id
let hash a = a.id land max_int

let print out s = Format.pp_print_string out s.name

let to_string s = s.name
