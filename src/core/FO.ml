
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 First-Order Monomorphic Terms} *)

module ID = ID
module Var = Var

type id = ID.t
type 'a var = 'a Var.t
type 'a printer = Format.formatter -> 'a -> unit

module TyBuiltin = struct
  type t =
    [ `Prop
    ]
  let equal = (=)
  let print out = function
    | `Prop -> CCFormat.string out "prop"
end

module Builtin = struct
  type t =
    [ `Int of int
    ]
  let equal = (=)
  let print out = function
    | `Int n -> CCFormat.int out n
end

(** Term *)
type ('t, 'ty) view =
  | Builtin of Builtin.t
  | Var of 'ty var
  | App of id * 't list
  | DataTest of id * 't
  | DataSelect of id * int * 't
  | Undefined of id * 't (** ['t] is not defined here *)
  | Fun of 'ty var * 't  (** caution, not supported everywhere *)
  | Mu of 'ty var * 't   (** caution, not supported everywhere *)
  | Let of 'ty var * 't * 't
  | Ite of 't * 't * 't
  | True
  | False
  | Eq of 't * 't
  | And of 't list
  | Or of 't list
  | Not of 't
  | Imply of 't * 't
  | Equiv of 't * 't
  | Forall of 'ty var * 't
  | Exists of 'ty var * 't

(** Type *)
type 'ty ty_view =
  | TyBuiltin of TyBuiltin.t
  | TyApp of id * 'ty list

(** Toplevel type: an arrow of atomic types *)
type 'ty toplevel_ty = 'ty list * 'ty

type 'ty constructor = {
  cstor_name: id;
  cstor_args: 'ty list; (* each arg: (selector, type) *)
}

type 'ty tydef = {
  ty_name: id;
  ty_cstors: 'ty constructor ID.Map.t;
}

type 'ty mutual_types = {
  tys_vars: id list;  (* type parameters *)
  tys_defs : 'ty tydef list;
}

(** Statement *)
type ('t, 'ty) statement =
  | TyDecl of id * int  (** number of arguments *)
  | Decl of id * 'ty toplevel_ty
  | Axiom of 't
  | MutualTypes of [`Data | `Codata] * 'ty mutual_types
  | Goal of 't

(** {2 Read-Only View} *)
module type VIEW = sig
  module Ty : sig
    type t
    type toplevel_ty = t list * t
    val view : t -> t ty_view
  end

  module T : sig
    type t
    val view : t -> (t, Ty.t) view
    (** Observe the structure of the term *)
  end
end

(** {2 View and Build Formulas, Terms, Types} *)
module type S = sig
  module Ty : sig
    type t
    type toplevel_ty = t list * t

    val view : t -> t ty_view

    val const : id -> t
    val app : id -> t list -> t
    val builtin : TyBuiltin.t -> t
    val arrow : t list -> t -> toplevel_ty
  end

  module T : sig
    type t
    val view : t -> (t, Ty.t) view
    (** Observe the structure of the term *)

    val builtin : Builtin.t -> t
    val const : id -> t
    val app : id -> t list -> t
    val data_test : id -> t -> t
    val data_select : id -> int -> t -> t
    val undefined : id -> t -> t
    val var : Ty.t var -> t
    val let_ : Ty.t var -> t -> t -> t
    val fun_ : Ty.t var -> t -> t
    val mu : Ty.t var -> t -> t
    val ite : t -> t -> t -> t
    val true_ : t
    val false_ : t
    val eq : t -> t -> t
    val and_ : t list -> t
    val or_ : t list -> t
    val not_ : t -> t
    val imply : t -> t -> t
    val equiv : t -> t -> t
    val forall : Ty.t var -> t -> t
    val exists : Ty.t var -> t -> t
  end
end

type ('t, 'ty) repr =
  (module VIEW with type T.t = 't and type Ty.t = 'ty)

type ('t, 'ty) build =
  (module S with type T.t = 't and type Ty.t = 'ty)

module Default : S = struct
  module Ty = struct
    type t = {
      view: t ty_view;
    }
    type toplevel_ty = t list * t

    let view t = t.view

    let make_ view = {view}
    let const id = make_ (TyApp (id, []))
    let app id l = make_ (TyApp (id, l))
    let builtin b = make_ (TyBuiltin b)
    let arrow a l = a,l
  end

  module T = struct
    type t = { view : (t, Ty.t) view }

    let view t = t.view

    let make_ view = {view}
    let builtin b = make_ (Builtin b)
    let app id l = make_ (App(id,l))
    let const id = make_ (App(id,[]))
    let var v = make_ (Var v)
    let data_test c t = make_ (DataTest (c,t))
    let data_select c n t = make_ (DataSelect (c,n,t))
    let undefined c t = make_ (Undefined (c,t))
    let let_ v t u = make_ (Let(v,t,u))
    let fun_ v t = make_ (Fun (v,t))
    let mu v t = make_ (Mu (v,t))
    let ite f t u = make_ (Ite (f,t,u))
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
      | {view=Not f; _} -> f
      | f -> make_ (Not f)
    let imply a b = make_ (Imply (a,b))
    let equiv a b = make_ (Equiv (a,b))
    let forall v t = make_ (Forall (v,t))
    let exists v t = make_ (Exists (v,t))
  end
end

let default_repr
: (Default.T.t, Default.Ty.t) repr
= (module Default : VIEW
     with type T.t = Default.T.t
     and type Ty.t = Default.Ty.t)

let default
: (Default.T.t, Default.Ty.t) build
= (module Default : S
     with type T.t = Default.T.t
     and type Ty.t = Default.Ty.t)

(** {2 The Problems sent to Solvers} *)
module Problem = struct

  type ('t, 'ty) t = {
    statements: ('t, 'ty) statement CCVector.ro_vector;
  }

  let make l = {statements=l}
  let of_list l = make (CCVector.of_list l)
  let statements t = t.statements

  let fold_flat_map f acc pb =
    let res = CCVector.create () in
    let acc' = CCVector.fold
      (fun acc st ->
        let acc, stmts = f acc st in
        CCVector.append_list res stmts;
        acc)
      acc pb.statements
    in
    let pb' = make (CCVector.freeze res) in
    acc', pb'
end

module type PRINT = sig
  module FO : VIEW

  val print_ty : FO.Ty.t printer
  val print_toplevel_ty : FO.Ty.toplevel_ty printer
  val print_term : FO.T.t printer
  val print_statement : (FO.T.t, FO.Ty.t) statement printer
  val print_model : (FO.T.t * FO.T.t) list printer
  val print_problem : (FO.T.t, FO.Ty.t) Problem.t printer
end

(* TODO: use it in CVC4? or too specific, this is not SMT specific *)
module Print(FO : VIEW) : PRINT with module FO = FO = struct
  module FO = FO

  let fpf = Format.fprintf

  let pp_list_ ?(sep=" ") out p = CCFormat.list ~start:"" ~stop:"" ~sep out p

  let rec print_ty out ty = match FO.Ty.view ty with
    | TyApp (id, []) -> ID.print out id
    | TyApp (id, l) ->
        fpf out "@[<2>(%a@ %a)@]" ID.print id (pp_list_ print_ty) l
    | TyBuiltin b -> TyBuiltin.print out b

  let print_toplevel_ty out (args, ret) =
    if args=[] then print_ty out ret
    else fpf out "@[<2>(%a -> %a)@]" (pp_list_ ~sep:" × " print_ty) args print_ty ret

  let rec print_term out t = match FO.T.view t with
    | Builtin b -> Builtin.print out b
    | Var v -> Var.print_full out v
    | App (f,[]) -> ID.print out f
    | App (f,l) ->
        fpf out "(@[<2>%a@ %a@])" ID.print f (pp_list_ print_term) l
    | Fun (v,t) ->
        fpf out "(@[<2>fun %a:%a.@ %a@])"
          Var.print_full v print_ty (Var.ty v) print_term t
    | Mu (v,t) ->
        fpf out "(@[<2>mu %a.@ %a@])" Var.print_full v print_term t
    | DataTest (c,t) ->
        fpf out "(@[<2>is-%a@ %a@])" ID.print c print_term t
    | DataSelect (c,n,t) ->
        fpf out "(@[<2>select-%a-%d@ %a@])" ID.print c n print_term t
    | Undefined (c,t) ->
        fpf out "(@[<2>undefined-%a@ %a@])" ID.print c print_term t
    | Let (v,t,u) ->
        fpf out "(@[<2>let@ %a =@ %a in@ %a@])"
          Var.print_full v print_term t print_term u
    | Ite (a,b,c) ->
        fpf out "(@[<2>ite@ %a@ %a@ %a@])"
          print_term a print_term b print_term c
    | True -> CCFormat.string out "true"
    | False -> CCFormat.string out "false"
    | Eq (a,b) -> fpf out "(@[%a =@ %a@])" print_term a print_term b
    | And l -> fpf out "(@[and@ %a@])" (pp_list_ print_term) l
    | Or l ->  fpf out "(@[and@ %a@])" (pp_list_ print_term) l
    | Not f -> fpf out "(@[not@ %a@])" print_term f
    | Imply (a,b) -> fpf out "(@[%a =>@ %a@])" print_term a print_term b
    | Equiv (a,b) -> fpf out "(@[%a <=>@ %a@])" print_term a print_term b
    | Forall (v,f) ->
        fpf out "(@[forall %a@ %a@])" Var.print_full v print_term f
    | Exists (v,f) ->
        fpf out "(@[forall %a@ %a@])" Var.print_full v print_term f

  let print_model out m =
    let pp_pair out (t,u) = fpf out "@[%a -> %a@]" print_term t print_term u in
    fpf out "@[model {@,@[<hv>%a@]}@]"
      (CCFormat.list ~start:"" ~stop:"" ~sep:","  pp_pair) m

  let print_statement out s = match s with
    | TyDecl (id, n) ->
        fpf out "@[<2>type %a (arity %d).@]" ID.print id n
    | Decl (v, ty) ->
        fpf out "@[<2>val %a@ : %a.@]" ID.print v print_toplevel_ty ty
    | Axiom t -> fpf out "@[<2>axiom %a.@]" print_term t
    | MutualTypes (k, l) ->
        let pp_arg = print_ty in
        let pp_tyvars_ out = function
          | [] -> ()
          | l -> fpf out "pi %a. " (pp_list_ ID.print) l
        in
        let pp_cstor out c = match c.cstor_args with
          | [] -> ID.print out c.cstor_name
          | _ ->
              fpf out "@[<2>(%a@ %a)@]" ID.print c.cstor_name
                (pp_list_ ~sep:" " pp_arg) c.cstor_args
        in
        let print_tydef out tydef =
          fpf out "@[<hv2>%a :=@ %a@]"
            ID.print tydef.ty_name
            (pp_list_ ~sep:" | " pp_cstor)
            (ID.Map.to_list tydef.ty_cstors |> List.map snd)
        in
        fpf out "@[<hv2>%s %a@,%a.@]"
          (match k with `Data -> "data" | `Codata -> "codata")
          pp_tyvars_ l.tys_vars
          (pp_list_ ~sep:" and " print_tydef) l.tys_defs
    | Goal t -> fpf out "@[<2>goal %a.@]" print_term t

  let print_problem out pb =
    fpf out "@[<v>%a@]"
      (CCVector.print ~start:"" ~stop:"" ~sep:"" print_statement)
      (Problem.statements pb)
end
