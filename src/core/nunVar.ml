
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

let fresh_copies l = List.map fresh_copy l

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

module type SUBST = sig
  type ty
  type var = ty t

  type 'a t
  (** A substitution for those variables *)

  val empty : 'a t
  val is_empty : _ t -> bool

  val add : subst:'a t -> var -> 'a -> 'a t

  val add_list : subst:'a t -> var list -> 'a list -> 'a t
  (** [add_list ~subst v t] add each binding [v_i -> t_i] to the subst.
      @raise Invalid_argument if [List.length v <> List.length t] *)

  val remove : subst:'a t -> var -> 'a t
  (** Remove binding for this variable.
      {b careful} if other bindings depend on this variable's binding... *)

  val mem : subst:'a t -> var -> bool
  val find : subst:'a t -> var -> 'a option
  val find_exn : subst:'a t -> var -> 'a  (** @raise Not_found if var not bound *)

  val to_list : 'a t -> (var * 'a) list
end

module Subst(Ty : sig type t end) : SUBST with type ty = Ty.t = struct
  type ty = Ty.t
  type var = Ty.t t

  module M = Map.Make(struct
    type t = var
    let compare = compare
  end)

  type 'a t = 'a M.t

  let empty = M.empty
  let is_empty = M.is_empty

  let add ~subst v x = M.add v x subst

  let rec add_list ~subst v t = match v, t with
    | [], [] -> subst
    | [], _
    | _, [] -> invalid_arg "Subst.add_list"
    | v :: v', t :: t' -> add_list ~subst:(add ~subst v t) v' t'

  let remove ~subst v = M.remove v subst

  let mem ~subst v = M.mem v subst

  let find_exn ~subst v = M.find v subst

  let find ~subst v = try Some (find_exn ~subst v) with Not_found -> None

  let to_list s = M.fold (fun v x acc -> (v,x)::acc) s []
end

module Set(Ty : sig type t end) = CCSet.Make(struct
  type 'a _t = 'a t
  type t = Ty.t _t
  let compare = compare
end)
