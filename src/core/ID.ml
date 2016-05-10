
(* This file is free software, part of nunchaku. See file "license" for more details. *)

type t = {
  name: string;
  id: int;
  needs_at: bool;
  pol: Polarity.t;
}
type _t = t

(* make fresh variables *)
let make_full =
  let n = ref 0 in
  fun ?(pol=Polarity.NoPol) ~needs_at name ->
    if name="" then invalid_arg "ID.make";
    let id = !n in
    incr n;
    {name; id; needs_at; pol; }

let make n = make_full ~needs_at:false n

let make_f msg = CCFormat.ksprintf msg ~f:make

let fresh_copy v = make_full ~needs_at:v.needs_at ~pol:v.pol v.name

let name v = v.name
let id v = v.id
let polarity v = v.pol
let needs_at v = v.needs_at

let is_pos v = v.pol = Polarity.Pos
let is_neg v = v.pol = Polarity.Neg
let is_neutral v = v.pol = Polarity.NoPol
let is_polarized v = not (is_neutral v)

let equal v1 v2 = v1.id = v2.id
let compare v1 v2 = Pervasives.compare v1.id v2.id
let hash_fun v h = CCHash.int v.id h
let hash v = v.id land max_int (* >= 0 *)

let print out v =
  if v.needs_at
    then Format.fprintf out "@@%s%s" v.name (Polarity.to_string v.pol)
    else Format.fprintf out "%s%s" v.name (Polarity.to_string v.pol)

let to_string v =
  if v.needs_at
    then Printf.sprintf "@@%s%s" v.name (Polarity.to_string v.pol)
    else v.name ^ Polarity.to_string v.pol

let to_string_slug v =
  let suffix = match v.pol with
    | Polarity.Pos -> "_pos"
    | Polarity.Neg -> "_neg"
    | Polarity.NoPol -> ""
  in
  v.name ^ suffix

let print_full out v =
  if v.needs_at
    then Format.fprintf out "@@%s%s/%d" v.name (Polarity.to_string v.pol) v.id
    else Format.fprintf out "%s%s/%d" v.name (Polarity.to_string v.pol) v.id

let print_name out v = CCFormat.string out v.name

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

module Erase = struct
  type state = {
    id_to_name : string Tbl.t;
    name_to_id : (string, t) Hashtbl.t;
  }

  let create_state () = {
    id_to_name = Tbl.create 32;
    name_to_id = Hashtbl.create 16;
  }

  let spf = CCFormat.sprintf

  let add_name state name id =
    if Tbl.mem state.id_to_name id then invalid_arg "ID.Erase.add_name";
    Tbl.add state.id_to_name id name;
    Hashtbl.add state.name_to_id name id;
    ()

  (* add numeric suffix to [name] until it is an unused name *)
  let find_unique_name_ state name0 =
    if not (Hashtbl.mem state.name_to_id name0) then name0
    else (
      let n = ref 0 in
      while Hashtbl.mem state.name_to_id (spf "%s_%d" name0 !n) do incr n done;
      spf "%s_%d" name0 !n
    )

  let to_name state id =
    try Tbl.find state.id_to_name id
    with Not_found ->
      let name = CCFormat.to_string print_name id |> find_unique_name_ state in
      Hashtbl.add state.name_to_id name id;
      Tbl.add state.id_to_name id name;
      name

  let of_name state n = Hashtbl.find state.name_to_id n
end
