
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 First-Order Monomorphic Terms} *)

module Metadata = ProblemMetadata
module Res = Problem.Res

type id = ID.t
type 'a var = 'a Var.t
type 'a printer = Format.formatter -> 'a -> unit
type 'a or_error = ('a, string) CCResult.t
type ('a,'b) res = ('a,'b) Res.t
type metadata = Metadata.t

module TyBuiltin = struct
  type t =
    [ `Prop
    | `Unitype
    ]
  let equal = (=)
  let compare = Pervasives.compare
  let pp out = function
    | `Unitype -> CCFormat.string out "unitype"
    | `Prop -> CCFormat.string out "prop"
end

module Builtin = struct
  type t =
    [ `Int of int
    ]
  let equal = (=)
  let compare = Pervasives.compare
  let pp out = function
    | `Int n -> CCFormat.int out n
end

(** Term *)
type ('t, 'ty) view =
  | Builtin of Builtin.t
  | Var of 'ty var
  | App of id * 't list
  | DataTest of id * 't
  | DataSelect of id * int * 't
  | Undefined of 't (** ['t] is not defined here *)
  | Undefined_atom of id * 'ty toplevel_ty * 't list (** some undefined term of given type, + args *)
  | Unparsable of 'ty (** could not parse term *)
  | Card_at_least of 'ty * int
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

(** Toplevel type: an arrow of atomic types *)
and 'ty toplevel_ty = 'ty list * 'ty

(** Type *)
type 'ty ty_view =
  | TyBuiltin of TyBuiltin.t
  | TyApp of id * 'ty list

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

type attr =
  | Attr_pseudo_prop
  | Attr_pseudo_true
  | Attr_card_hint of [`Max | `Min] * int (** cardinality bound hint *)
  | Attr_can_be_empty

(** Statement *)
type ('t, 'ty) statement =
  | TyDecl of id * int * attr list (** number of arguments *)
  | Decl of id * 'ty toplevel_ty * attr list
  | Axiom of 't
  | CardBound of id * [`Max | `Min] * int (** cardinality bound *)
  | MutualTypes of [`Data | `Codata] * 'ty mutual_types
  | Goal of 't

module Ty = struct
  type t = {
    view: t ty_view;
  }
  type _t = t
  type toplevel_ty = t list * t

  let view t = t.view

  let make_ view = {view}
  let const id = make_ (TyApp (id, []))
  let app id l = make_ (TyApp (id, l))
  let builtin b = make_ (TyBuiltin b)
  let arrow a l = a,l

  let is_prop t = match t.view with
    | TyBuiltin `Prop -> true
    | _ -> false

  let to_int_ = function
    | TyBuiltin _ -> 0
    | TyApp _ -> 1

  let rec compare_ty t1 t2 = match t1.view, t2.view with
    | TyBuiltin b1, TyBuiltin b2 -> TyBuiltin.compare b1 b2
    | TyApp (c1,l1), TyApp (c2,l2) ->
      CCOrd.( ID.compare c1 c2 <?> (list compare_ty, l1, l2))
    | TyApp _, _
    | TyBuiltin _, _ -> Pervasives.compare (to_int_ t1.view) (to_int_ t2.view)

  let hash t = match t.view with
    | TyBuiltin _ -> 3
    | TyApp (id, _) -> ID.hash id

  let compare = compare_ty
  let equal a b = compare a b = 0

  let to_seq t yield =
    let rec aux t =
      yield t;
      begin match t.view with
        | TyBuiltin _ -> ()
        | TyApp (_,l) -> List.iter aux l
      end
    in
    aux t
end

module T = struct
  type t = { view : (t, Ty.t) view; id: int }

  let view t = t.view
  let compare a b = Pervasives.compare a.id b.id

  let make_ =
    let n = ref 0 in
    fun view ->
      let t = {view; id= !n } in
      incr n;
      t

  (* very naive hash *)
  let hash t = match t.view with
    | Var v -> ID.hash (Var.id v)
    | App (id,_) -> ID.hash id
    | _ -> 42

  let rec equal t1 t2 = match t1.view, t2.view with
    | True, True
    | False, False -> true
    | App (f1,l1), App (f2,l2) ->
      ID.equal f1 f2 && CCList.equal equal l1 l2
    | Var v1, Var v2 -> Var.equal v1 v2
    | Undefined t1, Undefined t2 -> equal t1 t2
    | DataTest (i1,t1), DataTest(i2,t2) -> ID.equal i1 i2 && equal t1 t2
    | DataSelect (i1,n1,t1), DataSelect(i2,n2,t2) ->
      ID.equal i1 i2 && n1=n2 && equal t1 t2
    | Undefined_atom (i1,_,l1), Undefined_atom (i2,_,l2) ->
      ID.equal i1 i2 && CCList.equal equal l1 l2
    | Builtin b1, Builtin b2 -> Builtin.equal b1 b2
    | Unparsable ty1, Unparsable ty2 -> Ty.equal ty1 ty2
    | Forall (v1,t1), Forall (v2,t2)
    | Exists (v1,t1), Exists (v2,t2)
    | Mu (v1,t1), Mu (v2,t2)
    | Fun (v1,t1), Fun (v2,t2) -> Var.equal v1 v2 && equal t1 t2
    | Let (v1,t1,u1), Let (v2,t2,u2) ->
      Var.equal v1 v2 && equal t1 t2 && equal u1 u2
    | Ite (a1,b1,c1), Ite (a2,b2,c2) ->
      equal a1 a2 && equal b1 b2 && equal c1 c2
    | And l1, And l2
    | Or l1, Or l2 -> CCList.equal equal l1 l2
    | Not a, Not b -> equal a b
    | Imply (a1,b1), Imply (a2,b2)
    | Equiv (a1,b1), Equiv (a2,b2) -> equal a1 a2 && equal b1 b2
    | Card_at_least (ty1,n1), Card_at_least (ty2,n2) -> Ty.equal ty1 ty2 && n1=n2
    | True, _ | False, _ | App _, _ | Var _, _ | Undefined _, _
    | Undefined_atom _, _ | DataSelect _, _ | DataTest _, _
    | Forall _, _ | Exists _, _ | Mu _, _ | Fun _, _
    | Let _, _ | Ite _, _ | And _, _ | Or _, _ | Not _, _
    | Imply _, _ | Equiv _, _ | Eq _, _ | Builtin _, _
    | Unparsable _, _ | Card_at_least _, _
      -> false

  let builtin b = make_ (Builtin b)
  let app id l = make_ (App(id,l))
  let const id = make_ (App(id,[]))
  let var v = make_ (Var v)
  let data_test c t = make_ (DataTest (c,t))
  let data_select c n t = make_ (DataSelect (c,n,t))
  let undefined t = make_ (Undefined t)
  let undefined_atom c ty l = make_ (Undefined_atom (c,ty,l))
  let unparsable ty = make_ (Unparsable ty)
  let card_at_least ty n = make_ (Card_at_least (ty,n))
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
    | l when List.exists (function {view=False; _} -> true | _ -> false) l -> false_
    | l -> make_ (And l)
  let or_ = function
    | [] -> false_
    | [x] -> x
    | l when List.exists (function {view=True; _} -> true | _ -> false) l -> true_
    | l -> make_ (Or l)
  let not_ = function
    | {view=True; _} -> false_
    | {view=False; _} -> true_
    | {view=Not f; _} -> f
    | f -> make_ (Not f)
  let imply a b = match a.view, b.view with
    | True, _ -> b
    | False, _ -> true_
    | _, False -> not_ a
    | _ -> make_ (Imply (a,b))
  let equiv a b = make_ (Equiv (a,b))
  let forall v t = make_ (Forall (v,t))
  let exists v t = make_ (Exists (v,t))

  let is_var = function {view=Var _; _} -> true | _ -> false

  let to_seq t yield =
    let rec aux t =
      yield t;
      begin match t.view with
        | True | False | Var _ | Builtin (`Int _)
        | Unparsable _ | Card_at_least _
          -> ()
        | And l | Or l | Undefined_atom (_,_,l) | App (_,l)
          -> List.iter aux l
        | DataTest (_,t)
        | DataSelect (_,_,t)
        | Undefined t
        | Fun (_,t)
        | Mu (_,t)
        | Forall (_,t)
        | Exists (_,t)
        | Not t
          -> aux t
        | Let (_,t,u) -> aux t; aux u
        | Ite (a,b,c) -> aux a; aux b; aux c
        | Eq (a,b) | Imply (a,b) | Equiv (a,b) -> aux a; aux b
      end
    in
    aux t
end

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

  let map ~meta f pb = flat_map ~meta (fun s -> [f s]) pb

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

  let to_seq t = CCVector.to_seq t.statements
end

let tys_of_toplevel_ty (l,ret) yield =
  List.iter yield l; yield ret

let st_to_seq_ t ~term:yield_term ~ty:yield_ty = match t with
  | TyDecl (_,_,_) -> ()
  | Decl (_,ty,_) -> tys_of_toplevel_ty ty yield_ty
  | Axiom t -> yield_term t
  | CardBound (_,_,_) -> ()
  | MutualTypes (_,defs) ->
    Sequence.of_list defs.tys_defs
    |> Sequence.flat_map (fun tydef -> ID.Map.values tydef.ty_cstors)
    |> Sequence.flat_map_l (fun cstor -> cstor.cstor_args)
    |> Sequence.iter yield_ty
  | Goal t -> yield_term t

let terms_of_statement st yield = st_to_seq_ st ~term:yield ~ty:(fun _ -> ())
let tys_of_statement st yield = st_to_seq_ st ~term:(fun _ -> ()) ~ty:yield

let fpf = Format.fprintf

let pp_list_ ?(sep=" ") out p = Utils.pp_list ~sep out p

let rec pp_ty out ty = match Ty.view ty with
  | TyApp (id, []) -> ID.pp out id
  | TyApp (id, l) ->
    fpf out "@[<2>(%a@ %a)@]" ID.pp id (pp_list_ pp_ty) l
  | TyBuiltin b -> TyBuiltin.pp out b

let pp_toplevel_ty out (args, ret) =
  if args=[] then pp_ty out ret
  else fpf out "@[<2>(%a -> %a)@]" (pp_list_ ~sep:" × " pp_ty) args pp_ty ret

let rec pp_term out t = match T.view t with
  | Builtin b -> Builtin.pp out b
  | Var v -> Var.pp_full out v
  | App (f,[]) -> ID.pp out f
  | App (f,l) ->
    fpf out "(@[<2>%a@ %a@])" ID.pp f (pp_list_ pp_term) l
  | Fun (v,t) ->
    fpf out "(@[<2>fun %a:%a.@ %a@])"
      Var.pp_full v pp_ty (Var.ty v) pp_term t
  | Mu (v,t) ->
    fpf out "(@[<2>mu %a.@ %a@])" Var.pp_full v pp_term t
  | DataTest (c,t) ->
    fpf out "(@[<2>is-%a@ %a@])" ID.pp c pp_term t
  | DataSelect (c,n,t) ->
    fpf out "(@[<2>select-%a-%d@ %a@])" ID.pp c n pp_term t
  | Undefined t ->
    fpf out "(@[<2>undefined@ %a@])" pp_term t
  | Undefined_atom (c,ty,[]) ->
    fpf out "(@[<2>undefined-%a@ ty:%a@])" ID.pp c pp_toplevel_ty ty
  | Undefined_atom (c,ty,l) ->
    fpf out "(@[<2>undefined-%a@ ty:%a@ %a@])"
      ID.pp c pp_toplevel_ty ty (pp_list_ pp_term) l
  | Unparsable ty ->
    fpf out "(@[<2>unparsable ty:%a@])" pp_ty ty
  | Card_at_least (ty,n) ->
    fpf out "(@[card(%a) ≥ %d@])" pp_ty ty n
  | Let (v,t,u) ->
    fpf out "(@[<2>let@ %a =@ %a in@ %a@])"
      Var.pp_full v pp_term t pp_term u
  | Ite (a,b,c) ->
    fpf out "(@[<2>ite@ %a@ %a@ %a@])"
      pp_term a pp_term b pp_term c
  | True -> CCFormat.string out "true"
  | False -> CCFormat.string out "false"
  | Eq (a,b) -> fpf out "(@[%a =@ %a@])" pp_term a pp_term b
  | And l -> fpf out "(@[<hv1>and@ %a@])" (pp_list_ pp_term) l
  | Or l ->  fpf out "(@[<hv1>or@ %a@])" (pp_list_ pp_term) l
  | Not f -> fpf out "(@[not@ %a@])" pp_term f
  | Imply (a,b) -> fpf out "(@[<hv>%a@ =>@ %a@])" pp_term a pp_term b
  | Equiv (a,b) -> fpf out "(@[<hv>%a@ <=>@ %a@])" pp_term a pp_term b
  | Forall (v,f) ->
    fpf out "(@[forall %a@ %a@])" Var.pp_full v pp_term f
  | Exists (v,f) ->
    fpf out "(@[exists %a@ %a@])" Var.pp_full v pp_term f

let pp_term' _prec = pp_term

let pp_model out m =
  let pp_pair out (t,u) = fpf out "@[%a -> %a@]" pp_term t pp_term u in
  fpf out "@[model {@,@[<hv>%a@]}@]"
    (Utils.pp_list  ~sep:","  pp_pair) m

let pp_attr out = function
  | Attr_pseudo_prop -> fpf out "pseudo_prop"
  | Attr_pseudo_true -> fpf out "pseudo_true"
  | Attr_card_hint (`Max, n) -> fpf out "max_card_hint %d" n
  | Attr_card_hint (`Min, n) -> fpf out "min_card_hint %d" n
  | Attr_can_be_empty -> CCFormat.string out "can_be_empty"

let pp_attrs out = function
  | [] -> ()
  | l -> fpf out " [@[%a@]]" (pp_list_ ~sep:"," pp_attr) l

let pp_statement out s = match s with
  | TyDecl (id, n, attrs) ->
    fpf out "@[<2>type %a (arity %d%a).@]" ID.pp id n pp_attrs attrs
  | Decl (v, ty, attrs) ->
    fpf out "@[<2>val %a@ : %a%a.@]" ID.pp v pp_toplevel_ty ty pp_attrs attrs
  | Axiom t -> fpf out "@[<2>axiom %a.@]" pp_term t
  | CardBound (ty_id, which, n) ->
    let s = match which with `Max -> "max_card" | `Min -> "min_card" in
    fpf out "@[<2>%s %a@ = %d.@]" s ID.pp ty_id n
  | MutualTypes (k, l) ->
    let pp_arg = pp_ty in
    let pp_tyvars_ out = function
      | [] -> ()
      | l -> fpf out "pi %a. " (pp_list_ ID.pp) l
    in
    let pp_cstor out c = match c.cstor_args with
      | [] -> ID.pp out c.cstor_name
      | _ ->
        fpf out "@[<2>(%a@ %a)@]" ID.pp c.cstor_name
          (pp_list_ ~sep:" " pp_arg) c.cstor_args
    in
    let pp_tydef out tydef =
      fpf out "@[<hv2>%a :=@ %a@]"
        ID.pp tydef.ty_name
        (pp_list_ ~sep:" | " pp_cstor)
        (ID.Map.to_list tydef.ty_cstors |> List.map snd)
    in
    fpf out "@[<hv2>%s %a@,%a.@]"
      (match k with `Data -> "data" | `Codata -> "codata")
      pp_tyvars_ l.tys_vars
      (pp_list_ ~sep:" and " pp_tydef) l.tys_defs
  | Goal t -> fpf out "@[<2>goal %a.@]" pp_term t

let pp_problem out pb =
  fpf out "@[<v>%a@]"
    (Utils.pp_seq ~sep:"" pp_statement)
    (Problem.statements pb |> CCVector.to_seq)

(** {2 Utils} *)
module Util = struct
  module DT = Model.DT

  (* condition: var = term *)
  type cond = (T.t, Ty.t) DT.flat_test

  exception Parse_err of unit lazy_t
  (* evaluate the lazy -> pp a warning *)

  let mk_eq = DT.mk_flat_test
  let mk_true v = mk_eq v T.true_

  (* split [t] into a list of equations [var = t'] where [var in vars] *)
  let rec get_eqns_exn ~vars t : cond list =
    Utils.debugf 5 "get_eqns @[%a@]" (fun k->k pp_term t);
    let fail() =
      let msg = lazy (
        Utils.warningf Utils.Warn_model_parsing_error
          "expected a test <var = term>@ with <var> among @[%a@],@ but got `@[%a@]`@]"
          (CCFormat.list Var.pp_full) vars pp_term t
      ) in
      raise (Parse_err msg)
    in
    match T.view t with
      | And l -> CCList.flat_map (get_eqns_exn ~vars) l
      | Eq (t1, t2) ->
        begin match T.view t1, T.view t2 with
          | Var v, _ when List.exists (Var.equal v) vars -> [mk_eq v t2]
          | _, Var v when List.exists (Var.equal v) vars -> [mk_eq v t1]
          | _ -> fail()
        end
      | Var v when List.exists (Var.equal v) vars ->
        assert (Ty.is_prop (Var.ty v));
        [mk_true v]
      | Var _ ->
        let msg = lazy (
          Utils.warningf Utils.Warn_model_parsing_error
            "expected a boolean variable among @[%a@],@ but got @[%a@]@]"
            (CCFormat.list Var.pp_full) vars pp_term t
        ) in
        raise (Parse_err msg)
      | _ -> fail()

  let get_eqns ~vars t : cond list option =
    try Some (get_eqns_exn ~vars t)
    with Parse_err _ -> None

  module Ite_M = struct
    (* returns a sequence of (conditions, 'a).
       Invariant: the last element of the sequence is exactly the only
       one with an empty list of conditions *)
    type +'a t = (cond list * 'a) Sequence.t

    let return x : _ t = Sequence.return ([], x)

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
    let case
      : type a. cond list -> a t -> a t -> a t
      = fun cond a b ->
        (* remove trivial tests [v=v] *)
        let cond =
          List.filter
            (fun {DT.ft_var=v; ft_term=t} -> match T.view t with
               | Var v' -> not (Var.equal v v')
               | _ -> true)
            cond
        in
        let a' =
          Sequence.map
            (fun (cond',ret) -> List.rev_append cond cond', ret)
            a
        in
        Sequence.append a' b

    let ite
      : type a. Ty.t Var.t -> a t -> a t -> a t
      = fun v a b -> case [mk_true v] a b

    let rec fold_m f acc l = match l with
      | [] -> return acc
      | x :: tail ->
        f acc x >>= fun acc -> fold_m f acc tail

    (* convert to a decision tree. *)
    let to_dt ~vars t : (_,_) DT.t =
      (* tests must have >= 1 condition; otherwise they are default *)
      let tests, others =
        Sequence.to_list t
        |> List.partition (fun (tests,_) -> tests<>[])
      in
      let default = match others with
        | [] -> None
        | ([],t)::_ -> Some t
        | _ -> assert false
      in
      let fdt =
        {DT.
          fdt_vars=vars;
          fdt_cases=tests;
          fdt_default=default;
        }
      in
      DT.of_flat ~equal:T.equal ~hash:T.hash fdt
  end

  let dt_of_term ~vars t =
    let open Ite_M in
    let rec aux t : T.t Ite_M.t =
      match T.view t with
        | Builtin _
        | DataTest (_,_)
        | DataSelect (_,_,_)
        | Undefined _
        | Undefined_atom _
        | Unparsable _ | Card_at_least _
        | Mu (_,_)
        | True
        | False
        | Let _
        | Fun _
        | Equiv (_,_)
        | Forall (_,_)
        | Exists (_,_) -> return t
        | Var v when Ty.is_prop (Var.ty v)  ->
          (* boolean variable: perform a test on it *)
          ite v (return T.true_) (return T.false_)
        | Var _ -> return t
        | Eq (a,b) ->
          begin match get_eqns ~vars t with
            | Some conds ->
              (* yield true if equality holds, false otherwise *)
              case conds (return T.true_) (return T.false_)
            | None ->
              aux a >>= fun a ->
              aux b >|= fun b -> T.eq a b
          end
        | Imply (a,b) ->
          begin match get_eqns ~vars a with
            | Some conds ->
              (* a => b becomes if a then b else false *)
              case conds (aux b) (return T.false_)
            | None ->
              aux a >>= fun a ->
              aux b >|= fun b ->
              T.imply a b
          end
        | Ite (a,b,c) ->
          let cond = get_eqns_exn ~vars a in
          case cond (aux b) (aux c)
        | And l ->
          begin match get_eqns ~vars t with
            | Some cond ->
              case cond (return T.true_) (return T.false_)
            | None -> aux_l l >|= T.and_
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
      Ite_M.to_dt ~vars res
    with Parse_err msg ->
      (* return "unparsable" *)
      Lazy.force msg;
      DT.yield (T.unparsable (Ty.builtin `Prop))

  let problem_kinds pb =
    let module M = Model in
    let add_stmt m = function
      | TyDecl (id, _, _) -> ID.Map.add id M.Symbol_utype m
      | Decl (id, (_, ret), _) ->
        let k = match Ty.view ret with
          | TyBuiltin `Prop -> M.Symbol_prop
          | TyBuiltin `Unitype
          | TyApp _ -> M.Symbol_fun
        in
        ID.Map.add id k m
      | Axiom _
      | CardBound _
      | Goal _ -> m
      | MutualTypes (d, tydefs) ->
        let d = match d with
          | `Data -> M.Symbol_data
          | `Codata -> M.Symbol_codata
        in
        List.fold_left
          (fun m tydef ->
             let m = ID.Map.add tydef.ty_name d m in
             ID.Map.fold (fun id _ m -> ID.Map.add id M.Symbol_fun m) tydef.ty_cstors m)
          m tydefs.tys_defs
    in
    CCVector.fold add_stmt ID.Map.empty (Problem.statements pb)
end
