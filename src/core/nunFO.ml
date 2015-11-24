
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 First-Order Monomorphic Terms} *)

module ID = NunID
module Var = NunVar

type id = NunID.t
type 'a var = 'a NunVar.t
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
type ('f, 't, 'ty) view =
  | Builtin of Builtin.t
  | Var of 'ty var
  | App of id * 't list
  | DataTest of id * 't
  | DataSelect of id * int * 't
  | Fun of 'ty var * 't  (** caution, not supported everywhere *)
  | Let of 'ty var * 't * 't
  | Ite of 'f * 't * 't

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
  | F_let of 'ty var * 'f * 'f
  | F_ite of 'f * 'f * 'f  (* if then else *)
  | F_fun of 'ty var * 'f (* function *)

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

(** Problem *)
type ('f, 't, 'ty) statement =
  | TyDecl of id * int  (** number of arguments *)
  | Decl of id * 'ty toplevel_ty
  | Axiom of 'f
  | MutualTypes of [`Data | `Codata] * 'ty mutual_types
  | Goal of 'f

(** models, for instance, might contain both formulas and terms *)
type ('t, 'f) term_or_form =
  | Term of 't
  | Form of 'f

type ('t, 'f) term_or_form_ = ('t, 'f) term_or_form
(** Alias for avoiding recursive defs *)

(** {2 Read-Only View} *)
module type VIEW = sig
  type formula

  module Ty : sig
    type t
    type toplevel_ty = t list * t
    val view : t -> t ty_view
  end

  module T : sig
    type t
    val view : t -> (formula, t, Ty.t) view
    (** Observe the structure of the term *)
  end

  module Formula : sig
    type t = formula
    val view : t -> (t, T.t, Ty.t) form_view
  end

  type term_or_form = (T.t, Formula.t) term_or_form_
end

(** {2 View and Build Formulas, Terms, Types} *)
module type S = sig
  type formula

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
    val view : t -> (formula, t, Ty.t) view
    (** Observe the structure of the term *)

    val builtin : Builtin.t -> t
    val const : id -> t
    val app : id -> t list -> t
    val data_test : id -> t -> t
    val data_select : id -> int -> t -> t
    val var : Ty.t var -> t
    val let_ : Ty.t var -> t -> t -> t
    val fun_ : Ty.t var -> t -> t
    val ite : formula -> t -> t -> t
  end

  module Formula : sig
    type t = formula

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
    val f_let : Ty.t var -> t -> t -> t
    val f_ite : t -> t -> t -> t
    val f_fun : Ty.t var -> t -> t

    val map : (T.t -> T.t) -> t -> t
  end

  type term_or_form = (T.t, Formula.t) term_or_form_
end

type ('f, 't, 'ty) repr =
  (module VIEW with type formula = 'f and type T.t = 't and type Ty.t = 'ty)

type ('f, 't, 'ty) build =
  (module S with type formula = 'f and type T.t = 't and type Ty.t = 'ty)

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

  type term = { view : (formula, term, Ty.t) view }
  and formula = {
    fview: (formula, term, Ty.t) form_view;
  }

  module T = struct
    type t = term

    let view t = t.view

    let make_ view = {view}
    let builtin b = make_ (Builtin b)
    let app id l = make_ (App(id,l))
    let const id = make_ (App(id,[]))
    let var v = make_ (Var v)
    let data_test c t = make_ (DataTest (c,t))
    let data_select c n t = make_ (DataSelect (c,n,t))
    let let_ v t u = make_ (Let(v,t,u))
    let fun_ v t = make_ (Fun (v,t))
    let ite f t u = make_ (Ite (f,t,u))
  end

  module Formula = struct
    type t = formula

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
    let f_let v a b = make_ (F_let (v,a,b))
    let f_ite a b c = make_ (F_ite (a,b,c))
    let f_fun v t = make_ (F_fun (v,t))

    let rec map f form = match view form with
      | Atom t -> atom (f t)
      | True
      | False -> form
      | Eq (a,b) -> eq (f a) (f b)
      | And l -> and_ (List.map (map f) l)
      | Or l -> or_ (List.map (map f) l)
      | Not form -> not_ (map f form)
      | Imply (a,b) -> imply (map f a)(map f b)
      | Equiv (a,b) -> equiv (map f a)(map f b)
      | Forall (v,form) -> forall v (map f form)
      | Exists (v,form) -> exists v (map f form)
      | F_let (v,a,b) -> f_let v (map f a) (map f b)
      | F_ite (a,b,c) -> f_ite (map f a) (map f b) (map f c)
      | F_fun (v,t) -> f_fun v (map f t)
  end

  type term_or_form = (T.t, Formula.t) term_or_form_
end

let default_repr
: (Default.formula, Default.T.t, Default.Ty.t) repr
= (module Default : VIEW with type formula = Default.formula
     and type T.t = Default.T.t
     and type Ty.t = Default.Ty.t)

let default_build
: (Default.formula, Default.T.t, Default.Ty.t) build
= (module Default : S with type formula = Default.formula
     and type T.t = Default.T.t
     and type Ty.t = Default.Ty.t)

(** {2 The Problems sent to Solvers} *)
module Problem = struct
  type 'a vec_ro = ('a, CCVector.ro) CCVector.t

  type ('f, 't, 'ty) t = {
    statements: ('f, 't, 'ty) statement vec_ro;
  }

  let make l = {statements=l}
  let of_list l = make (CCVector.of_list l)
  let statements t = t.statements
end

module type PRINT = sig
  module FO : VIEW

  val print_ty : FO.Ty.t printer
  val print_toplevel_ty : FO.Ty.toplevel_ty printer
  val print_term : FO.T.t printer
  val print_formula : FO.Formula.t printer
  val print_statement : (FO.Formula.t, FO.T.t, FO.Ty.t) statement printer
  val print_model : (FO.T.t * FO.T.t) list printer
  val print_problem : (FO.Formula.t, FO.T.t, FO.Ty.t) Problem.t printer
end

(* TODO: use it in CVC4? or too specific, this is not SMT specific *)
module Print(FO : VIEW) : PRINT with module FO = FO = struct
  module FO = FO

  let fpf = Format.fprintf

  let pp_list_ ?(sep=" ") out p = CCFormat.list ~start:"" ~stop:"" ~sep out p

  let rec print_ty out ty = match FO.Ty.view ty with
    | TyApp (id, []) -> ID.print_no_id out id
    | TyApp (id, l) ->
        fpf out "@[<2>(%a@ %a)@]" ID.print_no_id id (pp_list_ print_ty) l
    | TyBuiltin b -> TyBuiltin.print out b

  let print_toplevel_ty out (args, ret) =
    if args=[] then print_ty out ret
    else fpf out "@[<2>(%a -> %a)@]" (pp_list_ ~sep:" × " print_ty) args print_ty ret

  let rec print_term out t = match FO.T.view t with
    | Builtin b -> Builtin.print out b
    | Var v -> Var.print out v
    | App (f,[]) -> ID.print_no_id out f
    | App (f,l) ->
        fpf out "(@[<2>%a@ %a@])" ID.print_no_id f (pp_list_ print_term) l
    | Fun (v,t) ->
        fpf out "(@[<2>fun %a:%a.@ %a@])"
          Var.print v print_ty (Var.ty v) print_term t
    | DataTest (c,t) ->
        fpf out "(@[<2>is-%a@ %a@])" ID.print_name c print_term t
    | DataSelect (c,n,t) ->
        fpf out "(@[<2>select-%a-%d@ %a@])" ID.print_name c n print_term t
    | Let (v,t,u) ->
        fpf out "(@[<2>let@ %a =@ %a in@ %a@])"
          Var.print v print_term t print_term u
    | Ite (a,b,c) ->
        fpf out "(@[<2>ite@ %a@ %a@ %a@])"
          print_formula a print_term b print_term c

  and print_formula out f = match FO.Formula.view f with
    | Atom t -> print_term out t
    | True -> CCFormat.string out "true"
    | False -> CCFormat.string out "false"
    | Eq (a,b) -> fpf out "(@[%a =@ %a@])" print_term a print_term b
    | And l -> fpf out "(@[and@ %a@])" (pp_list_ print_formula) l
    | Or l ->  fpf out "(@[and@ %a@])" (pp_list_ print_formula) l
    | Not f -> fpf out "(@[not@ %a@])" print_formula f
    | Imply (a,b) -> fpf out "(@[%a =>@ %a@])" print_formula a print_formula b
    | Equiv (a,b) -> fpf out "(@[%a <=>@ %a@])" print_formula a print_formula b
    | Forall (v,f) ->
        fpf out "(@[forall %a@ %a@])" Var.print v print_formula f
    | Exists (v,f) ->
        fpf out "(@[forall %a@ %a@])" Var.print v print_formula f
    | F_let (v,t,u) ->
        fpf out "@[<2>(let@ %a =@ %a in@ %a)@]"
          Var.print v print_formula t print_formula u
    | F_ite (a,b,c) ->
        fpf out "(@[f_ite %a@ %a@ %a@])"
          print_formula a print_formula b print_formula c
    | F_fun (v,t) ->
        fpf out "@[<2>(fun %a:%a.@ %a)@]"
          Var.print v print_ty (Var.ty v) print_formula t

  let print_model out m =
    let pp_pair out (t,u) = fpf out "@[%a -> %a@]" print_term t print_term u in
    fpf out "@[model {@,@[<hv>%a@]}@]"
      (CCFormat.list ~start:"" ~stop:"" ~sep:","  pp_pair) m

  let print_statement out s = match s with
    | TyDecl (id, n) ->
        fpf out "@[<2>type %a (arity %d).@]" ID.print_no_id id n
    | Decl (v, ty) ->
        fpf out "@[<2>val %a@ : %a.@]" ID.print_no_id v print_toplevel_ty ty
    | Axiom t -> fpf out "@[<2>axiom %a.@]" print_formula t
    | MutualTypes (k, l) ->
        let pp_arg = print_ty in
        let pp_tyvars_ out = function
          | [] -> ()
          | l -> fpf out "pi %a. " (pp_list_ ID.print_name) l
        in
        let pp_cstor out c = match c.cstor_args with
          | [] -> ID.print_name out c.cstor_name
          | _ ->
              fpf out "@[<2>(%a@ %a)@]" ID.print_name c.cstor_name
                (pp_list_ ~sep:" " pp_arg) c.cstor_args
        in
        let print_tydef out tydef =
          fpf out "@[<hv2>%a :=@ %a@]"
            ID.print_name tydef.ty_name
            (pp_list_ ~sep:" | " pp_cstor)
            (ID.Map.to_list tydef.ty_cstors |> List.map snd)
        in
        fpf out "@[<hv2>%s %a@,%a.@]"
          (match k with `Data -> "data" | `Codata -> "codata")
          pp_tyvars_ l.tys_vars
          (pp_list_ ~sep:" and " print_tydef) l.tys_defs
    | Goal t -> fpf out "@[<2>goal %a.@]" print_formula t

  let print_problem out pb =
    fpf out "@[<v>%a@]"
      (CCVector.print ~start:"" ~stop:"" ~sep:"" print_statement)
      (Problem.statements pb)
end
