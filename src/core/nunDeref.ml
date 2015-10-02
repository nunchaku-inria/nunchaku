
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 References for Unification} *)

(** Pointer to another type *)
type 'a t = {
  mutable deref : 'a option;
}

let create() = { deref=None }

let deref t = t.deref

let can_bind t = match t.deref with
  | None -> true
  | Some _ -> false

let bind ~ref x =
  if can_bind ref then ref.deref <- Some x else invalid_arg "Deref.bind"


let rebind ~ref x =
  if can_bind ref then invalid_arg "Deref.rebind" else ref.deref <- Some x
