
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 First-Order Monomorphic Terms} *)

module Metadata = ProblemMetadata

type id = ID.t
type 'a var = 'a Var.t
type 'a printer = Format.formatter -> 'a -> unit
type 'a or_error = [`Ok of 'a | `Error of string]

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
  | CardBound of id * [`Max | `Min] * int (** cardinality bound *)
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
      | {view=True; _} -> false_
      | {view=False; _} -> true_
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
    meta: Metadata.t;
  }

  let make ~meta l = { meta; statements=l; }
  let of_list ~meta l = make ~meta (CCVector.of_list l)
  let statements t = t.statements
  let meta t = t.meta

  let flat_map ~meta f pb =
    let res = CCVector.flat_map_list f pb.statements in
    make ~meta res

  let fold_flat_map ~meta f acc pb =
    let res = CCVector.create () in
    let acc' = CCVector.fold
      (fun acc st ->
        let acc, stmts = f acc st in
        CCVector.append_list res stmts;
        acc)
      acc pb.statements
    in
    let pb' = make ~meta (CCVector.freeze res) in
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
        fpf out "(@[exists %a@ %a@])" Var.print_full v print_term f

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
    | CardBound (ty_id, which, n) ->
        let s = match which with `Max -> "max_card" | `Min -> "min_card" in
        fpf out "@[<2>%s %a@ = %d.@]" s ID.print ty_id n
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

(** {2 Utils} *)
module Util(Repr : S) = struct
  module T = Repr.T
  module P = Print(Repr)

  (* internal error *)
  exception Error of string
  let error_ msg = raise (Error msg)
  let errorf_ msg = CCFormat.ksprintf msg ~f:error_

  (* split [t] into a list of equations [var = t'] where [var in vars] *)
  let rec get_eqns ~vars t =
    Utils.debugf 5 "get_eqns @[%a@]" (fun k->k P.print_term t);
    let fail() =
      errorf_ "expected a test <var = term>@ with var among @[%a@],@ but got @[%a@]@]"
        (CCFormat.list Var.print_full) vars P.print_term t
    in
    match T.view t with
    | And l -> CCList.flat_map (get_eqns ~vars) l
    | Eq (t1, t2) ->
        begin match T.view t1, T.view t2 with
          | Var v, _ when List.exists (Var.equal v) vars ->
              [v, t2]
          | _, Var v when List.exists (Var.equal v) vars ->
              [v, t1]
          | _ -> fail()
        end
    | Var v when List.exists (Var.equal v) vars ->
        [v, T.true_] (* boolean variable *)
    | Var _ ->
        errorf_ "expected a boolean variable among @[%a@],@ but got @[%a@]@]"
          (CCFormat.list Var.print_full) vars P.print_term t
    | _ -> fail()

  type cond = Repr.Ty.t Var.t * T.t

  module DT = Model.DT

  module Ite_M = struct
    (* returns a sequence of (conditions, 'a).
       Invariant: the last element of the sequence is exactly the only
       one with an empty list of conditions *)
    type +'a t = (cond list * 'a) Sequence.t

    let return x = Sequence.return ([], x)

    let (>|=)
    : 'a t -> ('a -> 'b) -> 'b t
    = fun x f ->
      let open Sequence.Infix in
      x >|= fun (conds, t) -> conds, f t

    let (>>=)
    : 'a t -> ('a -> 'b t) -> 'b t
    = fun x f ->
      let open Sequence.Infix in
      x >>= fun (conds, t) ->
      f t >|= fun (conds', t') -> List.rev_append conds' conds, t'

    (* add a test; if the test holds yield [b], else yield [c] *)
    let guard
    : cond list -> 'a -> 'a -> 'a t
    = fun a b c ->
      Sequence.doubleton (a, b) ([], c)

    let rec fold_m f acc l = match l with
      | [] -> return acc
      | x :: tail ->
          f acc x >>= fun acc -> fold_m f acc tail

    (* convert to a decision tree. Careful with the order of cases,
       we reverse twice. *)
    let to_dt t : _ DT.t =
      let l = Sequence.to_rev_list t in
      match l with
      | [] -> assert false
      | (_::_,_)::_ -> assert false
      | ([], else_) :: cases ->
          let cases = List.rev cases in
          DT.test cases ~else_
  end

  let dt_of_term ~vars t =
    let open Ite_M in
    let rec aux t : T.t Ite_M.t =
      match T.view t with
      | Builtin _
      | DataTest (_,_)
      | DataSelect (_,_,_)
      | Undefined (_,_)
      | Mu (_,_)
      | True
      | False
      | Let _
      | Fun _
      | Equiv (_,_)
      | Forall (_,_)
      | Exists (_,_) -> return t
      | Var v ->
          (* boolean variable: perform a test on it *)
          guard [v, T.true_] T.true_ T.false_
      | Eq (a,b) ->
          begin try
            (* yield true if equality holds, false otherwise *)
            let cond = get_eqns ~vars t in
            guard cond T.true_ T.false_
          with Error _ ->
            aux a >>= fun a ->
            aux b >|= fun b -> T.eq a b
          end
      | Imply (a,b) ->
          begin try
            (* a => b becomes if a then b else false *)
            let cond = get_eqns ~vars a in
            aux b >>= fun b ->
            guard cond b T.false_
          with Error _ ->
            aux a >>= fun a ->
            aux b >|= fun b ->
            T.imply a b
          end
      | Ite (a,b,c) ->
          let cond = get_eqns ~vars a in
          aux b >>= fun b ->
          aux c >>= fun c ->
          guard cond b c
      | And l ->
          begin try
            let cond = get_eqns ~vars t in
            guard cond T.true_ T.false_
          with Error _ ->
            aux_l l >|= T.and_
          end
      | Or l -> aux_l l >|= T.or_
      | Not t -> aux t >|= T.not_
      | App (id,l) -> aux_l l >|= T.app id
    and aux_l l =
      fold_m
        (fun l x -> aux x >|= fun y -> y :: l)
        [] l
       >|= List.rev
    in
    try
      let res = aux t in
      `Ok (Ite_M.to_dt res)
    with Error msg -> `Error msg

  let problem_kinds pb =
    let module M = Model in
    let add_stmt m = function
      | TyDecl (id, _) -> ID.Map.add id M.Symbol_utype m
      | Decl (id, (_, ret)) ->
          let k = match Repr.Ty.view ret with
            | TyBuiltin `Prop -> M.Symbol_prop
            | TyApp _ -> M.Symbol_fun
          in
          ID.Map.add id k m
      | Axiom _
      | CardBound _
      | Goal _ -> m
      | MutualTypes (_, tydefs) ->
          List.fold_left
            (fun m tydef ->
              let m = ID.Map.add tydef.ty_name M.Symbol_data m in
              ID.Map.fold (fun id _ m -> ID.Map.add id M.Symbol_fun m) tydef.ty_cstors m)
            m tydefs.tys_defs
    in
    CCVector.fold add_stmt ID.Map.empty (Problem.statements pb)
end
