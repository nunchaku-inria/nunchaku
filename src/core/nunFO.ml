
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 First-Order Monomorphic Terms} *)

module ID = NunID
module Var = NunVar

type id = NunID.t
type 'a var = 'a NunVar.t

module TyBuiltin = struct
  type t =
    | Prop
  let equal = (=)
  let print out = function
    | Prop -> CCFormat.string out "prop"
end

module Builtin = struct
  type t =
    | Int of int
  let equal = (=)
  let print out = function
    | Int n -> CCFormat.int out n
end

(** Term *)
type ('t, 'ty) view =
  | Builtin of Builtin.t
  | Var of 'ty var
  | App of id * 't list
  | Let of 'ty var * 't * 't

(** Formula *)
type ('f, 't, 'ty) form_view =
  | Atom of 't
  | True
  | False
  | Eq of 't * 't
  | And of 'f list
  | Or of 'f list
  | Not of 'f
  | Imply of 'f * 'f
  | Equiv of 'f * 'f
  | Forall of 'ty var * 'f
  | Exists of 'ty var * 'f

(** Type *)
type 'ty ty_view =
  | TyBuiltin of TyBuiltin.t
  | TyApp of id * 'ty list

(** {1 First-Order Formulas, Terms, Types} *)
module type S = sig
  module Ty : sig
    type t

    val view : t -> t ty_view

    type arrow = t list * t
    (** list of args, return *)

    val const : id -> t
    val app : id -> t list -> t
    val arrow : t list -> t -> arrow
  end

  module T : sig
    type t
    val view : t -> (t, Ty.t) view
    (** Observe the structure of the term *)

    val builtin : Builtin.t -> t
    val const : id -> t
    val app : id -> t list -> t
    val var : Ty.t var -> t
  end

  module Formula : sig
    type t

    val view : t -> (t, T.t, Ty.t) form_view

    val atom : T.t -> t
    val true_ : t
    val false_ : t
    val eq : T.t -> T.t -> t
    val and_ : t list -> t
    val or_ : t list -> t
    val not_ : t -> t
    val imply : t -> t -> t
    val equiv : t -> t -> t
    val forall : Ty.t var -> t -> t
    val exists : Ty.t var -> t -> t
  end
end

module Default : S = struct
  module Ty = struct
    type t = {
      view: t ty_view;
    }

    let view t = t.view

    type arrow = t list * t

    let make_ view = {view}
    let const id = make_ (TyApp (id, []))
    let app id l = make_ (TyApp (id, l))
    let arrow a l = a,l
  end

  module T = struct
    type t = {
      view : (t, Ty.t) view;
    }

    let view t = t.view

    let make_ view = {view}
    let builtin b = make_ (Builtin b)
    let app id l = make_ (App(id,l))
    let const id = make_ (App(id,[]))
    let var v = make_ (Var v)
  end

  module Formula = struct
    type t = {
      fview: (t, T.t, Ty.t) form_view;
    }

    let view t = t.fview

    let make_ fview = {fview}
    let atom t = make_ (Atom t)
    let true_ = make_ True
    let false_ = make_ False
    let eq a b = make_ (Eq (a,b))
    let and_ = function
      | [] -> true_
      | [x] -> x
      | l -> make_ (And l)
    let or_ = function
      | [] -> false_
      | [x] -> x
      | l -> make_ (Or l)
    let not_ = function
      | {fview=Not f; _} -> f
      | f -> make_ (Not f)
    let imply a b = make_ (Imply (a,b))
    let equiv a b = make_ (Equiv (a,b))
    let forall v t = make_ (Forall (v,t))
    let exists v t = make_ (Exists (v,t))
  end
end


