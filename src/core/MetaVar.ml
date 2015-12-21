
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 References for Unification} *)

module ID = ID

type id = ID.t

(** Pointer to another type *)
type 'a t = {
  id : id;
  mutable deref : 'a option;
}

let make ~name = {
  id=ID.make name;
  deref=None;
}

let id v = v.id

let equal v1 v2 = ID.equal v1.id v2.id

let deref v = v.deref

let can_bind v = match v.deref with
  | None -> true
  | Some _ -> false

let bound t = not (can_bind t)

let bind ~var x =
  if can_bind var then var.deref <- Some x else invalid_arg "MetaVar.bind"

let rebind ~var x =
  if can_bind var then invalid_arg "MetaVar.rebind" else var.deref <- Some x

let update ~f v =
  {v with deref=CCOpt.map f v.deref; }

let print oc v = Format.fprintf oc "?%a" ID.print_full v.id
let to_string v = "?" ^ ID.to_string v.id

