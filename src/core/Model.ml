(* This file is free software, part of nunchaku. See file "license" for more details. *)

module TI = TermInner

type 'a printer = Format.formatter -> 'a -> unit
type 'a to_sexp = 'a -> CCSexp.t

let fpf = Format.fprintf

(** {2 Decision Trees}

    A decision tree is a nested if/then/else used to describe functions
    over finite domains. *)

module DT = struct
  type ('t, 'ty) test = 'ty Var.t * 't (** Equation var=term *)
  type ('t, 'ty) tests = ('t,'ty) test list

  type (+'t, +'ty) t = {
    tests: (('t, 'ty) test list * 't) list;
      (* [(else) if v_1 = t_1 & ... & v_n = t_n then ...] *)

    else_ : 't;
      (* else t *)
  }

  let test l ~else_ = { tests=l; else_; }

  let yield x = test [] ~else_:x

  let test_flatten l ~else_ =
    let tests = match else_.tests with
      | [] -> l
      | l' -> l @ l'
    in
    { tests; else_ = else_.else_; }

  let ite a b c = match c.tests with
    | [] -> test [a,b] ~else_:c.else_
    | l ->
        test ((a,b) :: l) ~else_:c.else_

  let map ?var ~term ~ty t =
    let map_eqn ~term ~ty (v,t) =
      let v = match var with
        | None -> Var.update_ty ~f:ty v
        | Some f ->
            match f v with
            | Some v' -> v'
            | None -> Var.update_ty ~f:ty v
      in
      v, term t
    in
    let map_pair ~term ~ty (a,b) = List.map (map_eqn ~term ~ty) a, term b in
    { tests=List.map (map_pair ~term ~ty) t.tests;
      else_ = term t.else_;
    }

  let print_test pp out (v,t) = fpf out "@[<2>%a@ = @[%a@]@]" Var.print_full v pp t
  let print_tests pp = CCFormat.list ~start:"" ~stop:"" ~sep:" && " (print_test pp)
  let print_case pp out (eqns,t) =
    fpf out "@[<2>if @[%a@]@ then @[%a@]@]" (print_tests pp) eqns pp t

  let print pp out t =
    let pp_eqns = print_tests pp in
    match t.tests with
    | [] -> fpf out "@[%a@]" pp t.else_
    | [a,b] ->
        fpf out "@[@[<v2>@[<2>if@ @[<hv>%a@]@]@ @[<2>then@ %a@]@]@ @[<2>else@ %a@]@]"
          pp_eqns a pp b pp t.else_
    | (a,b) :: l ->
        let pp_pair out (a,b) =
          fpf out "@[<v2>@[<2>else if@ @[<hv>%a@]@]@ @[<2>then@ %a@]@]" pp_eqns a pp b in
        let pp_elif = CCFormat.list ~start:"" ~stop:"" ~sep:" " pp_pair in
        fpf out "@[<hv>@[<v2>@[<2>if@ %a@]@ @[<2>then@ %a@]@]@ %a@ @[<2>else@ %a@]@]"
          pp_eqns a pp b pp_elif l pp t.else_

  let to_sexp ft t : CCSexp.t =
    let lst = CCSexp.of_list in
    let str = CCSexp.atom in
    let eqn_to_sexp (v,t) = lst [str "="; str (Var.to_string_full v); ft t] in
    let eqns_to_sexp = function
      | [] -> str "true"
      | [v,t] -> eqn_to_sexp (v,t)
      | l -> lst (str "and" :: List.map eqn_to_sexp l)
    in
    List.fold_right
      (fun (eqns,then_) else_ ->
         lst [str "if"; eqns_to_sexp eqns; ft then_; else_])
      t.tests (ft t.else_)
end

type ('t,'ty) decision_tree = ('t,'ty) DT.t

module DT_util(T : TI.S) = struct
  module U = TermInner.Util(T)

  let eval ~subst dt =
    let open DT in
    let tests =
      CCList.find
        (fun (eqns,then_) ->
          (* evaluate the test *)
          if List.for_all
            (fun (v, rhs) ->
              let lhs = Var.Subst.find_exn ~subst v in
              U.equal_with ~subst lhs rhs)
            eqns
          then Some then_
          else None)
      dt.tests
    in
    let res = match tests with
      | None -> dt.else_
      | Some res -> res
    in
    U.eval ~subst res

  let to_term dt =
    let open DT in
    let conv_eqn (v,t) = U.eq (U.var v) t in
    let conv_eqns l = U.and_ (List.map conv_eqn l) in
    List.fold_right
      (fun (test, then_) else_ -> U.ite (conv_eqns test) then_ else_)
      dt.tests
      dt.else_
end

(** {2 Models} *)

type symbol_kind =
  | Symbol_prop
  | Symbol_fun
  | Symbol_utype
  | Symbol_data

type (+'t, +'ty) fun_def =
  ('t * 'ty Var.t list * ('t,'ty) decision_tree * symbol_kind)

type (+'t, +'ty) t = {
  constants: ('t * 't * symbol_kind) list;
    (* constant -> its interpretation *)

  funs: ('t, 'ty) fun_def list;
    (* fun * var list -> body *)

  finite_types: ('ty * ID.t list) list;
    (* type -> finite domain *)

  potentially_spurious: bool;
    (** the model might be spurious, i.e. some approximation made the
        translation unsound *)
}

let empty = {
  constants=[];
  funs=[];
  finite_types=[];
  potentially_spurious=false;
}

let empty_copy m = { empty with potentially_spurious = m.potentially_spurious; }

let add_const t tup = {t with constants = tup :: t.constants; }

let add_fun t f = {t with funs = f :: t.funs; }

let add_finite_type t ty dom =
  {t with finite_types = (ty, dom) :: t.finite_types; }

let map ~term:fterm ~ty:fty m = {
  m with
  constants=CCList.map (fun (x,y,k) -> fterm x, fterm y, k) m.constants;
  funs=CCList.map
    (fun (t,vars,dt,k) ->
      fterm t, List.map (Var.update_ty ~f:fty) vars, DT.map ~term:fterm ~ty:fty dt, k)
    m.funs;
  finite_types=List.map (fun (ty,l) -> fty ty, l) m.finite_types;
}

let filter_map ~constants ~funs ~finite_types m = {
  m with
  constants = CCList.filter_map constants m.constants;
  funs = CCList.filter_map funs m.funs;
  finite_types = CCList.filter_map finite_types m.finite_types;
}

let const_true_ _ = true
let const_unit_ _ = ()
let const_fst_ x _ = x

let filter
    ?(constants=const_true_)
    ?(funs=const_true_)
    ?(finite_types=const_true_)
    m
  =
  filter_map m
    ~constants:(fun x -> if constants x then Some x else None)
    ~funs:(fun x -> if funs x then Some x else None)
    ~finite_types:(fun x -> if finite_types x then Some x else None)

let iter ?(constants=const_unit_) ?(funs=const_unit_) ?(finite_types=const_unit_) m =
  List.iter constants m.constants;
  List.iter funs m.funs;
  List.iter finite_types m.finite_types;
  ()

let fold ?(constants=const_fst_) ?(funs=const_fst_) ?(finite_types=const_fst_) acc m =
  let acc = ref acc in
  iter m
    ~constants:(fun x -> acc := constants !acc x)
    ~funs:(fun x -> acc := funs !acc x)
    ~finite_types:(fun x -> acc := finite_types !acc x);
  !acc

let print pt pty out m =
  let pp_tyvar out v = fpf out "@[<2>(%a : %a)@]" Var.print_full v pty (Var.ty v) in
  let pplist ~sep pp = CCFormat.list ~sep ~start:"" ~stop:"" pp in
  let pp_const out (t,u,_) = fpf out "@[<2>val %a :=@ @[%a@]@]." pt t pt u in
  let pp_type out (ty,dom) =
    fpf out "@[<2>type @[%a@]@ :=@ {@[<hv>%a@]}@]."
      pty ty (pplist ~sep:", " ID.print) dom
  and pp_fun out (f,vars,dt,_) =
    fpf out "@[<2>val @[%a@]@ :=@ @[<v2>@[fun @[<hv>%a@]@].@ @[%a@]@]@]."
      pt f
      (pplist ~sep:" " pp_tyvar) vars
      (DT.print pt) dt
  in
  (* only print non-empty lists *)
  let pp_nonempty_list pp out l =
    if l=[] then ()
    else fpf out "@[<v>%a@]@," (pplist ~sep:"" pp) l
  in
  fpf out "@[<v>%a%a%a@]"
    (pp_nonempty_list pp_type) m.finite_types
    (pp_nonempty_list pp_const) m.constants
    (pp_nonempty_list pp_fun) m.funs

let str = CCSexp.atom
let lst = CCSexp.of_list

let to_sexp ft fty m : CCSexp.t =
  let id_to_sexp id = str (ID.to_string id) in
  let var_to_sexp v = lst [ str (Var.to_string_full v); fty (Var.ty v)] in
  let const_to_sexp (t,u,_) = lst [str "val"; ft t; ft u] in
  let ty_to_sexp (ty,dom) =
    lst [str "type"; fty ty; lst (List.map id_to_sexp dom)] in
  let fun_to_sexp (f,vars,dt,_) =
    let fun_ =
      lst
        [ str "fun"
        ; lst (List.map var_to_sexp vars)
        ; DT.to_sexp ft dt
        ]
    in
    lst [str "val"; ft f; fun_]
  in
  lst
    ( List.map ty_to_sexp m.finite_types
    @ List.map const_to_sexp m.constants
    @ List.map fun_to_sexp m.funs)
