
(* This file is free software, part of nunchaku. See file "license" for more details. *)

module ID = NunID

type id = ID.t

type 'ty t = {
  id: id;
  ty: 'ty;
}

let equal v1 v2 = ID.equal v1.id v2.id
let compare v1 v2 = ID.compare v1.id v2.id

let make ~ty ~name =
  let id = ID.make ~name in
  { ty; id }

let fresh_copy v =
  { v with id=ID.fresh_copy v.id }

let of_id ~ty id = {id;ty}

let ty t = t.ty
let id t = t.id

let fresh_update_ty v ~f =
  let ty = f v.ty in
  make ~ty ~name:(ID.name v.id)

let update_ty v ~f =
  let ty = f v.ty in
  { id=v.id; ty }

let print oc v = ID.print oc v.id
let to_string v = ID.to_string v.id

(** {2 Substitutions} *)

module Subst(Ty : sig type t end) = struct
  type var = Ty.t t

  module M = Map.Make(struct
    type t = var
    let compare = compare
  end)

  type 'a t = 'a M.t

  let empty = M.empty

  let add ~subst v x = M.add v x subst

  let mem ~subst v = M.mem v subst

  let find_exn ~subst v = M.find v subst

  let find ~subst v = try Some (find_exn ~subst v) with Not_found -> None

  let to_list s = M.fold (fun v x acc -> (v,x)::acc) s []
end

