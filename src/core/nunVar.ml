
(* This file is free software, part of nunchaku. See file "license" for more details. *)

type t = {
  name: string;
  id: int;
}

(* make fresh variables *)
let make =
  let n = ref 0 in
  fun ~name ->
    if name="" then invalid_arg "Var.make";
    let id = !n in
    incr n;
    {name; id;}

let fresh_copy v = make ~name:v.name

let name v = v.name
let id v = v.id

let equal v1 v2 = v1.id = v2.id
let compare v1 v2 = Pervasives.compare v1.id v2.id
let hash v = v.id land max_int (* >= 0 *)

let print out v = Format.fprintf out "%s/%d" v.name v.id
