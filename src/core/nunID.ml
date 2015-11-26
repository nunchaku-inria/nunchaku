
(* This file is free software, part of nunchaku. See file "license" for more details. *)

type t = {
  name: string;
  id: int;
  needs_at: bool;
}
type _t = t

(* make fresh variables *)
let make_full =
  let n = ref 0 in
  fun ~needs_at ~name ->
    if name="" then invalid_arg "Var.make";
    let id = !n in
    incr n;
    {name; id; needs_at; }

let make = make_full ~needs_at:false

let fresh_copy v = make ~name:v.name

let name v = v.name
let id v = v.id
let needs_at v = v.needs_at

let equal v1 v2 = v1.id = v2.id
let compare v1 v2 = Pervasives.compare v1.id v2.id
let hash_fun v h = CCHash.int v.id h
let hash v = v.id land max_int (* >= 0 *)

let print out v =
  if v.needs_at
    then Format.fprintf out "@@%s/%d" v.name v.id
    else Format.fprintf out "%s/%d" v.name v.id

let to_string v =
  if v.needs_at
    then Printf.sprintf "@@%s/%d" v.name v.id
    else Printf.sprintf "%s/%d" v.name v.id

let print_name out v = CCFormat.string out v.name

let print_no_id out v =
  if v.needs_at
    then (CCFormat.string out "@"; CCFormat.string out v.name)
    else CCFormat.string out v.name

module As_key = struct
  type t = _t
  let compare = compare
  let hash = hash
  let equal = equal
end

module Map = CCMap.Make(As_key)
module Set = CCSet.Make(As_key)
module Tbl = CCHashtbl.Make(As_key)
module PerTbl = CCPersistentHashtbl.Make(As_key)

