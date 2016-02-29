(* This file is free software, part of nunchaku. See file "license" for more details. *)

module TI = TermInner

type 'a printer = Format.formatter -> 'a -> unit
let fpf = Format.fprintf

let section = Utils.Section.make "model"

(** {2 Decision Trees}

    A decision tree is a nested if/then/else used to describe functions
    over finite domains. *)

module DT = struct
  type ('t, 'ty) test = 'ty Var.t * 't (** Equation var=term *)

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

  let print pp out t =
    let pp_eqns = print_tests pp in
    match t.tests with
    | [] -> fpf out "@[%a@]" pp t.else_
    | [a,b] ->
        fpf out "@[@[<2>if@ @[<hv>%a@]@]@ @[<2>then@ %a@]@ @[<2>else@ %a@]@]"
          pp_eqns a pp b pp t.else_
    | (a,b) :: l ->
        let pp_pair out (a,b) =
          fpf out "@[<2>else if@ @[<hv>%a@]@]@ @[<2>then@ %a@]" pp_eqns a pp b in
        let pp_elif = CCFormat.list ~start:"" ~stop:"" ~sep:" " pp_pair in
        fpf out "@[<hv>@[<2>if@ %a@]@ @[<2>then@ %a@]@ %a@ @[<2>else@ %a@]@]"
          pp_eqns a pp b pp_elif l pp t.else_
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

type (+'t, +'ty) t = {
  constants: ('t * 't) list;
    (* constant -> its interpretation *)

  funs: ('t * 'ty Var.t list * ('t,'ty) decision_tree) list;
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

let add_const t pair = {t with constants = pair :: t.constants; }

let add_fun t f = {t with funs = f :: t.funs; }

let add_finite_type t ty dom =
  {t with finite_types = (ty, dom) :: t.finite_types; }

let map ~term:fterm ~ty:fty m = {
  m with
  constants=CCList.map (fun (x,y) -> fterm x, fterm y) m.constants;
  funs=CCList.map
    (fun (t,vars,dt) ->
      fterm t, List.map (Var.update_ty ~f:fty) vars, DT.map ~term:fterm ~ty:fty dt)
    m.funs;
  finite_types=List.map (fun (ty,l) -> fty ty, l) m.finite_types;
}

let filter_map ~constants ~funs ~finite_types m = {
  m with
  constants = CCList.filter_map constants m.constants;
  funs = CCList.filter_map funs m.funs;
  finite_types = CCList.filter_map finite_types m.finite_types;
}

let iter ~constants ~funs ~finite_types m =
  List.iter constants m.constants;
  List.iter funs m.funs;
  List.iter finite_types m.finite_types;
  ()

let fold ~constants ~funs ~finite_types acc m =
  let acc = ref acc in
  iter m
    ~constants:(fun x -> acc := constants !acc x)
    ~funs:(fun x -> acc := funs !acc x)
    ~finite_types:(fun x -> acc := finite_types !acc x);
  !acc

let print pt pty out m =
  let pplist ~sep pp = CCFormat.list ~sep ~start:"" ~stop:"" pp in
  let pp_pair out (t,u) = fpf out "@[<2>val %a :=@ @[%a@]@]." pt t pt u in
  let pp_type out (ty,dom) =
    fpf out "@[<2>type @[%a@]@ :=@ {@[<hv>%a@]}@]."
      pty ty (pplist ~sep:", " ID.print) dom
  and pp_fun out (f,vars,dt) =
    fpf out "@[<2>val @[%a@]@ :=@ @[<2>@[fun %a@].@ @[%a@]@]@]."
      pt f
      (pplist ~sep:" " Var.print_full) vars
      (DT.print pt) dt
  in
  (* only print non-empty lists *)
  let pp_nonempty_list pp out l =
    if l=[] then ()
    else fpf out "@[<v>%a@]@," (pplist ~sep:"" pp) l
  in
  fpf out "@[<v>%a%a%a@]"
    (pp_nonempty_list pp_type) m.finite_types
    (pp_nonempty_list pp_pair) m.constants
    (pp_nonempty_list pp_fun) m.funs

module Util(T : TI.S) = struct
  module U = TI.Util(T)
  module Ty = TypeMono.Make(T)
  module Red = Reduce.Make(T)

  (* return a prefix for constants in the domain of this given type *)
  let pick_prefix_ ty =
    (* TODO: improve, to avoid collisions *)
    let id = U.head_sym ty in
    ID.name id

  (* compute a set of renaming rules for the model [m] *)
  let renaming_rules_of_model_ m =
    List.fold_left
      (fun acc (t, dom) ->
        let prefix = pick_prefix_ t in
        CCList.Idx.foldi
          (fun acc i id ->
            let name = CCFormat.sprintf "%s_%d" prefix i in
            let rhs = ID.make name in
            ID.Map.add id rhs acc)
          acc dom)
      ID.Map.empty
      m.finite_types

  let pp_rule_ out (l,r) =
    fpf out "%a → @[%a@]" ID.print l ID.print r

  (* rename [v] and add the renaming to [subst] *)
  let rename_copy_ subst v =
    let name = Format.sprintf "v_%d" (Var.Subst.size subst) in
    let v' = Var.make ~ty:(Var.ty v) ~name in
    Var.Subst.add ~subst v v', v'

  (* rewrite [t] using the set of rewrite rules *)
  let rec rewrite_term_ rules subst t =
    match T.repr t with
    | TI.Const id ->
        begin try
          let id' = ID.Map.find id rules in
          U.const id'
        with Not_found -> t
        end
    | TI.Var v ->
        begin try U.var (Var.Subst.find_exn ~subst v)
        with Not_found -> t
        end
    | _ ->
        let t =
          U.map subst t
            ~f:(rewrite_term_ rules)
            ~bind:rename_copy_
        in
        (* reduce the term *)
        Red.whnf t

  let rename m =
    let rules = renaming_rules_of_model_ m in
    Utils.debugf 5 ~section "@[<2>apply rewrite rules@ @[<v>%a@]@]"
      (fun k->k (CCFormat.seq ~start:"" ~stop:"" ~sep:"" pp_rule_) (ID.Map.to_seq rules));
    (* update domains *)
    let finite_types =
      let rename_id id =
        try ID.Map.find id rules
        with Not_found -> id
      in
      List.map
        (fun (t, dom) -> t, List.map rename_id dom)
        m.finite_types
    in
    (* rewrite every term *)
    let rw_nil = rewrite_term_ rules Var.Subst.empty in
    { m with
      finite_types;
      constants=List.map
        (fun (t,u) -> rw_nil t, rw_nil u)
        m.constants;
      funs=List.map
        (fun (t,vars,rhs) ->
          let t = rw_nil t in
          let subst, vars = Utils.fold_map rename_copy_ Var.Subst.empty vars in
          let rw_subst t = rewrite_term_ rules subst t in
          t, vars, DT.map ~var:(Var.Subst.find ~subst) ~term:rw_subst ~ty:rw_subst rhs)
        m.funs;
    }

  let pipe_rename ~print:must_print =
    Transform.backward ~name:"model_rename"
      (fun m ->
        let m' = rename m in
        if must_print then (
          let module P = TI.Print(T) in
          Format.printf "@[<v2>@{<Yellow>after model renaming@}:@ {@,%a@]}@."
            (print P.print P.print) m');
        m')
end
