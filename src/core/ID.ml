
(* This file is free software, part of nunchaku. See file "license" for more details. *)

module Fields = Bit_set.Make(struct end)

type fields = Fields.t

type t = {
  name: string;
  id: int;
  fields: Fields.t;
  pol: Polarity.t;
}
type _t = t

let field_needs_at = Fields.mk_field ()
(** Field to indicate whether printed [id] should be preceded by '@' *)

let field_distinct = Fields.mk_field ()
(** Field to indicate whether the [id] is distinct from
    every other ID that has this field. It is useful for evaluation
    purpose. *)

let () = Fields.freeze ()

(* make fresh variables *)
let make_inner_ =
  let n = ref 0 in
  fun ?(pol=Polarity.NoPol) ~fields name ->
    if name="" then invalid_arg "ID.make";
    let id = !n in
    if id < 0 then failwith "id counter overflow";
    incr n;
    {name; id; fields; pol; }

let make_fields = make_inner_

let make_full ?pol ?(distinct=false) ~needs_at name =
  let fields =
    Fields.empty
    |> Fields.set field_needs_at needs_at
    |> Fields.set field_distinct distinct
  in
  make_inner_ ?pol ~fields name

let make n = make_full ~needs_at:false n

let make_f msg = CCFormat.ksprintf msg ~f:make

let fresh_copy_name v s = make_inner_ ~fields:v.fields ~pol:v.pol s
let fresh_copy v = fresh_copy_name v v.name

let name v = v.name
let id v = v.id
let polarity v = v.pol

let fields v = v.fields
let needs_at v = Fields.get field_needs_at v.fields
let is_distinct v = Fields.get field_distinct v.fields

let is_pos v = v.pol = Polarity.Pos
let is_neg v = v.pol = Polarity.Neg
let is_neutral v = v.pol = Polarity.NoPol
let is_polarized v = not (is_neutral v)

let equal v1 v2 = v1.id = v2.id
let compare v1 v2 = Pervasives.compare v1.id v2.id
let hash v = CCHash.int v.id

(*
let pp_normal out v =
  let suffix = if is_distinct v then "!" else "" in
  if needs_at v
  then Format.fprintf out "@@%s%s%s" v.name (Polarity.to_string v.pol) suffix
  else Format.fprintf out "%s%s%s" v.name (Polarity.to_string v.pol) suffix

*)

let pp_normal out v =
  if needs_at v
  then Format.fprintf out "@@%s%s" v.name (Polarity.to_string v.pol)
  else Format.fprintf out "%s%s" v.name (Polarity.to_string v.pol)

let to_string_normal v =
  if needs_at v
  then Printf.sprintf "@@%s%s" v.name (Polarity.to_string v.pol)
  else v.name ^ Polarity.to_string v.pol

let to_string_slug v =
  let suffix = match v.pol with
    | Polarity.Pos -> "_pos"
    | Polarity.Neg -> "_neg"
    | Polarity.NoPol -> ""
  in
  v.name ^ suffix

let pp_full out v =
  if needs_at v
  then Format.fprintf out "@@%s%s/%d" v.name (Polarity.to_string v.pol) v.id
  else Format.fprintf out "%s%s/%d" v.name (Polarity.to_string v.pol) v.id

let to_string_full = CCFormat.to_string pp_full

let pp_name out v = CCFormat.string out v.name

(* debug mode: always print ID unique counters *)
let always_print_full_ = ref false

let () =
  Utils.Options.add_list
    [ ("--pp-id", Arg.Set always_print_full_, " always print IDs numbers");
    ]

let pp out v =
  if !always_print_full_ then pp_full out v else pp_normal out v

let to_string v =
  if !always_print_full_ then to_string_full v else to_string_normal v

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

  let to_name ?(encode=fun _ n->n) state id =
    try Tbl.find state.id_to_name id
    with Not_found ->
      let name =
        CCFormat.to_string pp_name id
        |> encode id
        |> find_unique_name_ state
      in
      Hashtbl.add state.name_to_id name id;
      Tbl.add state.id_to_name id name;
      name

  let of_name state n = Hashtbl.find state.name_to_id n
end
