(* This file is free software, part of nunchaku. See file "license" for more details. *)

module ID = NunID

type id = NunID.t

type 'ty t = 'ty NunID.Map.t

let empty = ID.Map.empty

let mem ~sigma id = ID.Map.mem id sigma
let find_exn ~sigma id = ID.Map.find id sigma
let find ~sigma id =
  try Some (find_exn ~sigma id)
  with Not_found -> None

let declare ~sigma id ty = ID.Map.add id ty sigma
