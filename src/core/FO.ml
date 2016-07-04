
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 First-Order Monomorphic Terms} *)

module Metadata = ProblemMetadata
module Res = Problem.Res

type id = ID.t
type 'a var = 'a Var.t
type 'a printer = Format.formatter -> 'a -> unit
type 'a or_error = ('a, string) CCResult.t

module TyBuiltin = struct
  type t =
    [ `Prop
    | `Unitype
    ]
  let equal = (=)
  let compare = Pervasives.compare
  let print out = function
    | `Unitype -> CCFormat.string out "unitype"
    | `Prop -> CCFormat.string out "prop"
end

module Builtin = struct
  type t =
    [ `Int of int
    ]
  let equal = (=)
  let compare = Pervasives.compare
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
  | Undefined_atom of id * 'ty * 't list (** some undefined term of given type, + args *)
  | Unparsable of 'ty (** could not parse term *)
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

type attr =
  | Attr_pseudo_prop
  | Attr_pseudo_true

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
      CCOrd.( ID.compare c1 c2 <?> (list_ compare_ty, l1, l2))
    | TyApp _, _
    | TyBuiltin _, _ -> Pervasives.compare (to_int_ t1.view) (to_int_ t2.view)

  let hash t = match t.view with
    | TyBuiltin _ -> 3
    | TyApp (id, _) -> ID.hash id

  let compare = compare_ty
  let equal a b = compare a b = 0
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

  let builtin b = make_ (Builtin b)
  let app id l = make_ (App(id,l))
  let const id = make_ (App(id,[]))
  let var v = make_ (Var v)
  let data_test c t = make_ (DataTest (c,t))
  let data_select c n t = make_ (DataSelect (c,n,t))
  let undefined c t = make_ (Undefined (c,t))
  let undefined_atom c ty l = make_ (Undefined_atom (c,ty,l))
  let unparsable ty = make_ (Unparsable ty)
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
end


let fpf = Format.fprintf

let pp_list_ ?(sep=" ") out p = CCFormat.list ~start:"" ~stop:"" ~sep out p

let rec print_ty out ty = match Ty.view ty with
  | TyApp (id, []) -> ID.print out id
  | TyApp (id, l) ->
    fpf out "@[<2>(%a@ %a)@]" ID.print id (pp_list_ print_ty) l
  | TyBuiltin b -> TyBuiltin.print out b

let print_toplevel_ty out (args, ret) =
  if args=[] then print_ty out ret
  else fpf out "@[<2>(%a -> %a)@]" (pp_list_ ~sep:" × " print_ty) args print_ty ret

let rec print_term out t = match T.view t with
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
  | Undefined_atom (c,ty,[]) ->
    fpf out "(@[<2>undefined-%a@ ty:%a@])" ID.print c print_ty ty
  | Undefined_atom (c,ty,l) ->
    fpf out "(@[<2>undefined-%a@ ty:%a@ %a@])"
      ID.print c print_ty ty (pp_list_ print_term) l
  | Unparsable ty ->
    fpf out "(@[<2>unparsable ty:%a@])" print_ty ty
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

let print_term' _prec = print_term

let print_model out m =
  let pp_pair out (t,u) = fpf out "@[%a -> %a@]" print_term t print_term u in
  fpf out "@[model {@,@[<hv>%a@]}@]"
    (CCFormat.list ~start:"" ~stop:"" ~sep:","  pp_pair) m

let print_attr out = function
  | Attr_pseudo_prop -> fpf out "pseudo_prop"
  | Attr_pseudo_true -> fpf out "pseudo_true"

let print_attrs out = function
  | [] -> ()
  | l -> fpf out " [@[%a@]]" (pp_list_ ~sep:"," print_attr) l

let print_statement out s = match s with
  | TyDecl (id, n, attrs) ->
    fpf out "@[<2>type %a (arity %d%a).@]" ID.print id n print_attrs attrs
  | Decl (v, ty, attrs) ->
    fpf out "@[<2>val %a@ : %a%a.@]" ID.print v print_toplevel_ty ty print_attrs attrs
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

(** {2 Utils} *)
module Util = struct
  (* condition: var = term *)
  type cond = Ty.t Var.t * T.t

  exception Parse_err of unit lazy_t
  (* evaluate the lazy -> print a warning *)

  (* split [t] into a list of equations [var = t'] where [var in vars] *)
  let rec get_eqns_exn ~vars t : cond list =
    Utils.debugf 5 "get_eqns @[%a@]" (fun k->k print_term t);
    let fail() =
      let msg = lazy (
        Utils.warningf Utils.Warn_model_parsing_error
        "expected a test <var = term>@ with <var> among @[%a@],@ but got `@[%a@]`@]"
        (CCFormat.list Var.print_full) vars print_term t
      ) in
      raise (Parse_err msg)
    in
    match T.view t with
    | And l -> CCList.flat_map (get_eqns_exn ~vars) l
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
        let msg = lazy (
          Utils.warningf Utils.Warn_model_parsing_error
            "expected a boolean variable among @[%a@],@ but got @[%a@]@]"
            (CCFormat.list Var.print_full) vars print_term t
        ) in
        raise (Parse_err msg)
    | _ -> fail()

  let get_eqns ~vars t : cond list option =
    try Some (get_eqns_exn ~vars t)
    with Parse_err _ -> None

  module DT = Model.DT

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
      Sequence.append
        (Sequence.map (fun (cond',a') -> List.rev_append cond cond', a') a)
        b

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
          (* last case must have empty condition *)
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
      | Undefined_atom _
      | Unparsable _
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
          case [v, T.true_] (return T.true_) (return T.false_)
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
      Ite_M.to_dt res
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

(** {2 Conversion} *)

module To_tptp = struct
  module TT = FO_tptp

  exception Error of string
  let () = Printexc.register_printer
      (function
        | (Error e) -> Some (Utils.err_sprintf "conversion to TPTP: %s" e)
        | _ -> None)

  let error_ msg = raise (Error msg)
  let errorf_ msg = Utils.exn_ksprintf ~f:error_ msg

  let is_unitype_ ty = match Ty.view ty with
    | TyBuiltin `Unitype ->  true
    | _ -> false

  (* check the type of [v] *)
  let conv_var v =
    if is_unitype_ (Var.ty v)
    then Var.set_ty v ~ty:TT.Unitype
    else errorf_ "variable `%a` does not have type `unitype`" Var.print_full v

  (* intermediate structure, for having only one conversion into terms and
     into formulas *)
  type term_or_form =
    | T of TT.term
    | F of TT.form

  (* convert term *)
  let rec conv_rec subst t : term_or_form = match T.view t with
    | Builtin _ -> assert false (* TODO *)
    | Var v ->
      begin match Var.Subst.find ~subst v with
        | Some t -> T t
        | None -> T (TT.var (conv_var v))
      end
    | App (f,l) -> T (TT.app f (List.map (conv_as_term subst) l))
    | Undefined (_,t) -> conv_rec subst t
    | Mu (_,_)
    | DataTest (_,_)
    | DataSelect (_,_,_)
    | Undefined_atom _
    | Unparsable _ ->
      errorf_ "cannot convert `@[%a@]` to TPTP" print_term t
    | Fun (_,_) -> errorf_ "cannot convert function `@[%a@]` to TPTP" print_term t
    | Let (v,t,u) ->
      (* expand `let` *)
      let t = conv_as_term subst t in
      let subst = Var.Subst.add ~subst v t in
      conv_rec subst u
    | Ite (_,_,_) -> error_ "fo_to_tptp: unexpected `ite`"
    | True -> T TT.true_
    | False -> T TT.false_
    | Eq (a,b) -> F (TT.eq (conv_as_term subst a) (conv_as_term subst b))
    | And l -> F (TT.and_ (List.map (conv_as_form subst) l))
    | Or l -> F (TT.or_ (List.map (conv_as_form subst) l))
    | Not f -> F (TT.not_ (conv_as_form subst f))
    | Imply (a,b) -> F (TT.imply (conv_as_form subst a) (conv_as_form subst b))
    | Equiv (a,b) -> F (TT.equiv (conv_as_form subst a) (conv_as_form subst b))
    | Forall (v,f) ->
      let v' = conv_var v in
      let subst = Var.Subst.add v (TT.var v') ~subst in
      F (TT.forall v' (conv_as_form subst f))
    | Exists (v,f) ->
      let v' = conv_var v in
      let subst = Var.Subst.add v (TT.var v') ~subst in
      F (TT.exists v' (conv_as_form subst f))

  and conv_as_term subst t = match conv_rec subst t with
    | T t -> t
    | F _ -> errorf_ "@[expected term,@ but `@[%a@]` is a formula@]" print_term t

  and conv_as_form subst t = match conv_rec subst t with
    | F t -> t
    | T t -> TT.atom t

  let conv_form = conv_as_form Var.Subst.empty

  let conv_statement st = match st with
    | TyDecl _
    | Decl _ -> None
    | MutualTypes _ -> errorf_ "@[cannot convert@ statement `@[%a@]`@]" print_statement st
    | CardBound _ -> assert false (* TODO warning? *)
    | Axiom f -> Some (TT.axiom (conv_form f))
    | Goal f -> Some (TT.axiom (conv_form f)) (* careful, not a conjecture *)

  let conv_problem pb =
    let res = CCVector.filter_map conv_statement (Problem.statements pb) in
    { FO_tptp.
      pb_statements=res;
      pb_meta=Problem.meta pb;
    }
end

module Of_tptp = struct
  module TT = FO_tptp

  let conv_ty = function
    | TT.Unitype -> Ty.builtin `Unitype

  let conv_var = Var.update_ty ~f:conv_ty

  let gen_undefined_ =
    let r = ref 0 in
    fun () ->
      let id = ID.make_f "undefined_%d" !r in
      incr r;
      id

  let rec conv_term = function
    | TT.App (id, args) -> T.app id (List.map conv_term args)
    | TT.Var v -> T.var (conv_var v)
    | TT.True -> T.true_
    | TT.False -> T.false_
    | TT.Undefined_atom l ->
      (* a new undefined atom of type "unitype" *)
      let l = List.map conv_term l in
      T.undefined_atom (gen_undefined_ ()) (Ty.builtin `Unitype) l

  let conv_form _ = assert false (* TODO *)
end

let pipe_tptp =
  let decode () res =
    Res.map res ~term:Of_tptp.conv_term ~ty:Of_tptp.conv_ty
  in
  Transform.make
    ~name:"conv_tptp"
    ~encode:(fun pb -> To_tptp.conv_problem pb, ()) ~decode
    ()
