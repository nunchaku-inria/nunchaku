
(* This file is free software, part of nunchaku. See file "license" for more details. *)

type t = {
  name: string;
  id: int;
}
type _t = t

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
let to_string v = Printf.sprintf "%s/%d" v.name v.id

let print_no_id out v = CCFormat.string out v.name

module As_key = struct
  type t = _t
  let compare = compare
  let hash = hash
  let equal = equal
end

module Map = CCMap.Make(As_key)
module Set = CCSet.Make(As_key)
module Tbl = CCHashtbl.Make(As_key)

