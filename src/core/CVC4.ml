
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Interface to CVC4} *)

module E = CCError
module Var = Var
module ID = ID
module Sol = Solver_intf
module FOI = FO

type id = ID.t

let section = Utils.Section.make "cvc4"

module DSexp = CCSexpM.MakeDecode(struct
  type 'a t = 'a
  let return x = x
  let (>>=) x f = f x
end)

type model_elt = FO.Default.term_or_form

module Make(FO_T : FO.S) : sig
  include Solver_intf.S
  with module FO_T = FO_T
  and module FOBack = FO.Default

  val print_problem : Format.formatter -> problem -> unit
end = struct
  module FO_T = FO_T
  module T = FO_T.T
  module Ty = FO_T.Ty
  module F = FO_T.Formula

  (* for the model *)
  module FOBack = FO.Default

  type problem = (FO_T.Formula.t, FO_T.T.t, FO_T.Ty.t) FO.Problem.t

  type decoded_sym =
    | ID of id (* regular fun *)
    | DataTest of id
    | DataSelect of id * int

  type model_query =
    | Q_const
        (* we want to know the value of this constant *)
    | Q_type of ID.t
        (* [id -> ty] means that [id : ty] is a dummy value, and we  want
           to know the finite domain of [ty] by asking [(fmf.card.val id)] *)

  type decode_state = {
    decode_tbl: (string, decoded_sym) Hashtbl.t;
      (* map (stringof ID) -> ID, and other builtins *)
    symbols : model_query ID.Map.t;
      (* set of symbols to ask values for in the model *)
  }

  let create_decode_state ~symbols = {
    decode_tbl=Hashtbl.create 32;
    symbols;
  }

  (* the solver is dealt with through stdin/stdout *)
  type t = {
    oc : out_channel;
    fmt : Format.formatter; (* prints on [oc] *)
    ic : in_channel;
    decode: decode_state;
    mutable sexp : DSexp.t;
    mutable closed : bool;
    mutable res : model_elt Sol.Res.t option;
  }

  let name = "cvc4"

  let peek_res t = t.res

  let close s =
    if not s.closed then (
      s.closed <- true;
      (* quite cvc4 and stop process *)
      Format.pp_print_flush s.fmt ();
      output_string s.oc "(exit)\n";
      flush s.oc;
      let _ = Unix.close_process (s.ic, s.oc) in
      (* release buffer *)
      s.sexp <- DSexp.make ~bufsize:5 (fun _ _ _ -> assert false);
    )

  let create_ ~timeout ~symbols () =
    if timeout < 0. then invalid_arg "CVC4.create: wrong timeout";
    let cmd = Printf.sprintf "cvc4 --tlimit-per=%d --lang smt --finite-model-find"
      (int_of_float (timeout *. 1000.)) in
    let ic, oc = Unix.open_process cmd in
    (* the [t] instance *)
    let s = {
      oc;
      fmt=Format.formatter_of_out_channel oc;
      ic;
      decode=create_decode_state ~symbols;
      closed=false;
      sexp=DSexp.make ~bufsize:4_000 (input ic);
      res=None;
    } in
    Gc.finalise close s; (* close on finalize *)
    s

  let fpf = Format.fprintf

  let pp_list ?(start="") ?(stop="") pp =
    CCFormat.list ~sep:" " ~start ~stop pp

  (* print problems. [on_id (to_string id) id] is called every time
      an id is printed.  *)
  let print_problem_ ~on_id =
    (* print ID and remember its name for parsing model afterward *)
    let rec print_id out id =
      let name = ID.name id in
      on_id name (ID id);
      CCFormat.string out name

    (* print [is-c] for a constructor [c] *)
    and print_tester out c =
      let name = Printf.sprintf "is-%s" (ID.name c) in
      on_id name (DataTest c);
      CCFormat.string out name

    (* print [select-c-n] to select the n-th argument of [c] *)
    and print_select out (c,n) =
      let name = Printf.sprintf "_select_%s_%d" (ID.name c) n in
      on_id name (DataSelect (c,n));
      CCFormat.string out name

    (* print type (a monomorphic type) in SMT *)
    and print_ty out ty = match Ty.view ty with
      | FOI.TyBuiltin b ->
          begin match b with
          | `Prop -> CCFormat.string out "Bool"
          end
      | FOI.TyApp (f, []) -> print_id out f
      | FOI.TyApp (f, l) ->
          fpf out "@[(%a@ %a)@]"
            print_id f (pp_list print_ty) l

    (* print type in SMT syntax *)
    and print_ty_decl out ty =
      let args, ret = ty in
      fpf out "%a %a" (pp_list ~start:"(" ~stop:")" print_ty) args print_ty ret

    and print_term out t = match T.view t with
      | FOI.Builtin b ->
          begin match b with
          | `Int n -> CCFormat.int out n
          end
      | FOI.Var v -> Var.print out v
      | FOI.App (f,[]) -> print_id out f
      | FOI.App (f,l) ->
          fpf out "(@[%a@ %a@])"
            print_id f (pp_list print_term) l
      | FOI.DataTest (c,t) ->
          fpf out "(@[%a@ %a@])" print_tester c print_term t
      | FOI.DataSelect (c,n,t) ->
          fpf out "(@[%a@ %a@])" print_select (c,n) print_term t
      | FOI.Undefined (_,t) -> print_term out t
      | FOI.Fun (v,t) ->
          fpf out "@[<3>(LAMBDA@ ((%a %a))@ %a)@]"
            Var.print v print_ty (Var.ty v) print_term t
      | FOI.Let (v,t,u) ->
          fpf out "@[<3>(let@ ((%a %a))@ %a@])"
            Var.print v print_term t print_term u
      | FOI.Ite (a,b,c) ->
          fpf out "@[<2>(ite@ %a@ %a@ %a)@]"
            print_form a print_term b print_term c

    and print_form out t = match F.view t with
      | FOI.Atom t -> print_term out t
      | FOI.True -> CCFormat.string out "true"
      | FOI.False -> CCFormat.string out "false"
      | FOI.Eq (a,b) -> fpf out "(@[=@ %a@ %a@])" print_term a print_term b
      | FOI.And [] -> CCFormat.string out "true"
      | FOI.And [f] -> print_form out f
      | FOI.And l ->
          fpf out "(@[and@ %a@])" (pp_list print_form) l
      | FOI.Or [] -> CCFormat.string out "false"
      | FOI.Or [f] -> print_form out f
      | FOI.Or l ->
          fpf out "(@[or@ %a@])" (pp_list print_form) l
      | FOI.Not f ->
          fpf out "(@[not@ %a@])" print_form f
      | FOI.Imply (a,b) ->
          fpf out "(@[=>@ %a@ %a@])" print_form a print_form b
      | FOI.Equiv (a,b) ->
          fpf out "(@[=@ %a@ %a@])" print_form a print_form b
      | FOI.Forall (v,f) ->
          fpf out "(@[<2>forall@ ((%a %a))@ %a@])"
            Var.print v print_ty (Var.ty v) print_form f
      | FOI.Exists (v,f) ->
          fpf out "(@[<2>exists@ ((%a %a))@ %a@])"
            Var.print v print_ty (Var.ty v) print_form f
      | FOI.F_let (v,t,u) ->
          fpf out "@[<3>(let@ ((%a %a))@ %a@])"
            Var.print v print_form t print_form u
      | FOI.F_ite (a,b,c) ->
          fpf out "@[<2>(ite@ %a@ %a@ %a)@]"
            print_form a print_form b print_form c
      | FOI.F_fun (v,t) ->
          fpf out "@[<3>(LAMBDA@ ((%a %a))@ %a)@]"
            Var.print v print_ty (Var.ty v) print_form t

    and print_statement out = function
      | FOI.TyDecl (id,arity) ->
          fpf out "(@[declare-sort@ %a@ %d@])" print_id id arity
      | FOI.Decl (v,ty) ->
          fpf out "(@[<2>declare-fun@ %a@ %a@])"
            print_id v print_ty_decl ty
      | FOI.Axiom t ->
          fpf out "(@[assert@ %a@])" print_form t
      | FOI.Goal t ->
          fpf out "(@[assert@ %a@])" print_form t
      | FOI.MutualTypes (k, l) ->
        let pp_arg out (c,i,ty) =
          fpf out "(@[<h>%a %a@])" print_select (c,i) print_ty ty in
        let pp_cstor out c =
          (* add selectors *)
          let args = List.mapi (fun i ty -> c.FOI.cstor_name,i,ty) c.FOI.cstor_args in
          fpf out "(@[<2>%a@ %a@])" ID.print_name c.FOI.cstor_name
            (pp_list pp_arg) args
        in
        let print_tydef out tydef =
          fpf out "(@[<2>%a@ %a@])"
            ID.print_name tydef.FOI.ty_name
            (pp_list pp_cstor) (ID.Map.to_list tydef.FOI.ty_cstors |> List.map snd)
        in
        fpf out "(@[<2>%s (%a) (%a)@])"
          (match k with `Data -> "declare-datatypes"
            | `Codata -> "declare-codatatypes")
          (pp_list ID.print_name) l.FOI.tys_vars
          (pp_list print_tydef) l.FOI.tys_defs

    in
    fun out pb ->
      (* send prelude *)
      fpf out "@[<v>";
      fpf out "(set-option :produce-models true)@,";
      fpf out "(set-option :interactive-mode true)@,";
      fpf out "(set-logic ALL_SUPPORTED)@,"; (* taïaut! *)
      (* write problem *)
      CCVector.print ~start:"" ~stop:"" ~sep:""
        print_statement out pb.FOI.Problem.statements;
      fpf out "@,(check-sat)@]@.";
      ()

  let send_ s problem =
    let on_id name def =
      Hashtbl.replace s.decode.decode_tbl name def
    in
    fpf s.fmt "%a@." (print_problem_ ~on_id) problem;
    ()

  let print_problem = print_problem_ ~on_id:(fun _ _ -> ())

  (* local error, should never escape *)
  exception Error of string

  let error_ e = raise (Error e)

  (* parse an identifier *)
  let parse_atom_ ~state = function
    | `Atom s ->
        begin try Hashtbl.find state.decode_tbl s
        with Not_found ->
          (* introduced by CVC4 in the model; make a new ID *)
          let id = ID.make ~name:s in
          Hashtbl.replace state.decode_tbl s (ID id);
          ID id
        end
    | _ -> error_ "expected ID, got a list"

  let parse_id_ ~state s = match parse_atom_ ~state s with
    | ID id -> id
    | DataTest _
    | DataSelect _ -> error_ "expected ID, got data test/select"

  (* parse an atomic type *)
  let rec parse_ty_ ~state = function
    | `Atom _ as f ->
        let id = parse_id_ ~state f in
        FOBack.Ty.const id
    | `List (`Atom _ as f :: l) ->
        let id = parse_id_ ~state f in
        let l = List.map (parse_ty_ ~state) l in
        FOBack.Ty.app id l
    | _ -> error_ "invalid type"

  let parse_var_ ~state = function
    | `List [`Atom _ as v; ty] ->
        let id = parse_id_ ~state v in
        let ty = parse_ty_ ~state ty in
        Var.of_id ~ty id
    | _ -> error_ "expected typed variable"

  (* is this formula actually just a term? if yes, convert *)
  let rec as_term_ f = match FOBack.Formula.view f with
    | FO.Atom t -> Some t
    | FO.F_fun (v,f) ->
        CCOpt.map (FOBack.T.fun_ v) (as_term_ f)
    | FO.F_let (v,t,u) ->
        CCOpt.map2 (FOBack.T.let_ v) (as_term_ t) (as_term_ u)
    | FO.True
    | FO.False
    | FO.Eq (_,_)
    | FO.And _
    | FO.Or _
    | FO.Not _
    | FO.Imply (_,_)
    | FO.Equiv (_,_)
    | FO.Forall (_,_)
    | FO.Exists (_,_)
    | FO.F_ite (_,_,_) -> None

  (* parse a ground term *)
  let rec parse_term_ ~state = function
    | `Atom _ as t -> FOBack.T.const (parse_id_ ~state t)
    | `List [`Atom "LAMBDA"; `List bindings; body] ->
        (* lambda term *)
        let bindings = List.map (parse_var_ ~state) bindings in
        let body = parse_term_ ~state body in
        List.fold_right FOBack.T.fun_ bindings body
    | `List [`Atom "ite"; a; b; c] ->
        let a = parse_formula_ ~state a in
        let b = parse_term_ ~state b in
        let c = parse_term_ ~state c in
        FOBack.T.ite a b c
    | `List (`Atom _ as f :: l) ->
        begin match parse_atom_ ~state f, l with
          | ID f, _ ->
              (* regular function app *)
              let l = List.map (parse_term_ ~state) l in
              FOBack.T.app f l
          | DataTest c, [t] ->
              let t = parse_term_ ~state t in
              FOBack.T.data_test c t
          | DataTest _, _ -> error_ "invalid arity for DataTest"
          | DataSelect (c,n), [t] ->
              let t = parse_term_ ~state t in
              FOBack.T.data_select c n t
          | DataSelect _, _ -> error_ "invalid arity for DataSelect"
        end
    | `List (`List _ :: _) -> error_ "non first-order list"
    | `List [] -> error_ "expected term, got empty list"

  and parse_formula_ ~state s =
    let module F = FOBack.Formula in
    match s with
    | `Atom "true" -> F.true_
    | `Atom "false" -> F.false_
    | `List [`Atom "="; a; b] ->
        let a = parse_term_or_formula_ ~state a in
        let b = parse_term_or_formula_ ~state b in
        begin match a, b with
        | FO.Term a,FO.Term b -> F.eq a b
        | FO.Form a,FO.Form b -> F.equiv a b
        | FO.Form a,FO.Term b -> F.equiv a (F.atom b)
        | FO.Term a,FO.Form b -> F.equiv (F.atom a) b
        end
    | `List [`Atom "not"; f] ->
        let f = parse_formula_ ~state f in
        F.not_ f
    | `List (`Atom "and" :: l) ->
        F.and_ (List.map (parse_formula_ ~state) l)
    | `List (`Atom "or" :: l) ->
        F.or_ (List.map (parse_formula_ ~state) l)
    | `List [`Atom "forall"; `List bindings; f] ->
        let bindings = List.map (parse_var_ ~state) bindings in
        let f = parse_formula_ ~state f in
        List.fold_right F.forall bindings f
    | `List [`Atom "exists"; `List bindings; f] ->
        let bindings = List.map (parse_var_ ~state) bindings in
        let f = parse_formula_ ~state f in
        List.fold_right F.exists bindings f
    | `List [`Atom "LAMBDA"; `List bindings; body] ->
        (* lambda term *)
        let bindings = List.map (parse_var_ ~state) bindings in
        let body = parse_formula_ ~state body in
        List.fold_right FOBack.Formula.f_fun bindings body
    | `List [`Atom "=>"; a; b] ->
        let a = parse_formula_ ~state a in
        let b = parse_formula_ ~state b in
        F.imply a b
    | `List [`Atom "ite"; a; b; c] ->
        let a = parse_formula_ ~state a in
        let b = parse_term_or_formula_ ~state b in
        let c = parse_term_or_formula_ ~state c in
        begin match b, c with
          | FO.Term b, FO.Term c ->
              F.atom (FOBack.T.ite a b c)
          | FO.Form b, FO.Form c -> F.f_ite a b c
          | FO.Form b, FO.Term c -> F.f_ite a b (F.atom c)
          | FO.Term b, FO.Form c -> F.f_ite a (F.atom b) c
        end
    | _ ->
        let t = parse_term_ ~state s in
        F.atom t

  and parse_term_or_formula_ ~state t =
    let f = parse_formula_ ~state t in
    (* [f] might be a term *)
    match as_term_ f with
    | None -> FO.Form f
    | Some t -> FO.Term t

  let parse_terms_ ~state = function
    | `List l ->
        List.map (fun s -> FO.Term (parse_term_ ~state s)) l
    | `Atom _ -> error_ "expected list of terms, got Atom"

  let sym_get_const_ ~state id = match ID.Map.find id state.symbols with
    | Q_const -> ()
    | Q_type _ -> assert false

  let sym_get_ty_ ~state id = match ID.Map.find id state.symbols with
    | Q_const -> assert false
    | Q_type ty -> ty

  (* state: decode_state *)
  let parse_model_ ~state = function
    | `Atom _ -> error_ "expected model, got atom"
    | `List assoc ->
      (* parse model *)
      let m = List.fold_left
        (fun m -> function
          | `List [`Atom _ as s; term] ->
              (* regular constant, whose value we are interested in *)
              let id = parse_id_ ~state s in
              sym_get_const_ ~state id;  (* check it's a constant *)
              let t = parse_term_or_formula_ ~state term in
              Model.add m (FO.Term (FOBack.T.const id), t)
          | `List [`List [`Atom "fmf.card.val"; (`Atom _ as s)]; l] ->
              (* finite domain *)
              let id = parse_id_ ~state s in
              (* which type? *)
              let ty_id = sym_get_ty_ ~state id in
              let ty = FO.Term (FOBack.T.const ty_id) in
              let terms = parse_terms_ ~state l in
              Model.add_finite_type m ty terms
          | _ -> error_ "expected pair key/value in the model")
        Model.empty
        assoc
      in
      m

  (* read model from CVC4 instance [s] *)
  let get_model_ ~state s : _ Model.t =
    Utils.debugf ~section 3 "@[<2>ask for values of@ %a@]"
      (fun k -> k
        (CCFormat.seq ~start:"(" ~sep:" " ~stop:")" ID.print_name)
        (ID.Map.to_seq state.symbols |> Sequence.map fst));
    (* print a single symbol *)
    let pp_mquery out (id, q) = match q with
      | Q_const -> ID.print_name out id
      | Q_type _ -> fpf out "(fmf.card.val %a)" ID.print_name id
    in
    fpf s.fmt "(@[<hv2>get-value@ %a@])@."
      (CCFormat.seq ~start:"(" ~sep:" " ~stop:")" pp_mquery)
      (ID.Map.to_seq state.symbols);
    (* read result back *)
    match DSexp.next s.sexp with
    | `Error e -> error_ e
    | `End -> error_ "unexpected end of input from CVC4: expected model"
    | `Ok sexp ->
        if !Sol.print_model_
          then Format.eprintf "@[raw model:@ @[<hv>%a@]@]@." CCSexpM.print sexp;
        let m = parse_model_ ~state sexp in
        (* check all symbols are defined *)
        let ok =
          List.length m.Model.terms + List.length m.Model.finite_types
          =
          ID.Map.cardinal state.symbols
        in
        if not ok then error_ "some symbols are not defined in the model";
        m

  (* rewrite model to be nicer
   TODO: CLI flag to opt-out?
   TODO: put this into Model? *)
  let rewrite_model_ m =
    (* rewrite [t] using the set of rewrite rules *)
    let rec rewrite_term_ ~rules t = match FOBack.T.view t with
      | FO.Builtin _
      | FO.Var _ -> t
      | FO.App (id,[]) ->
          begin try ID.Map.find id rules (* apply rule *)
          with Not_found -> t
          end
      | FO.DataTest(c,t) -> FOBack.T.data_test c (rewrite_term_ ~rules t)
      | FO.DataSelect(c,n,t) -> FOBack.T.data_select c n (rewrite_term_ ~rules t)
      | FO.Undefined _ -> assert false
      | FO.App (id, l) -> FOBack.T.app id (List.map (rewrite_term_ ~rules) l)
      | FO.Fun (v,t) ->
          (* no capture, rules rewrite to closed terms *)
          FOBack.T.fun_ v (rewrite_term_ ~rules t)
      | FO.Let (v,t,u) ->
          FOBack.T.let_ v (rewrite_term_ ~rules t) (rewrite_term_ ~rules u)
      | FO.Ite (a,b,c) ->
          FOBack.T.ite (rewrite_form_ ~rules a) (rewrite_term_ ~rules b) (rewrite_term_ ~rules c)
    and rewrite_form_ ~rules f =
      FOBack.Formula.map (rewrite_term_ ~rules) f
    in
    let rewrite_ ~rules = function
      | FO.Term t -> FO.Term (rewrite_term_ ~rules t)
      | FO.Form f -> FO.Form (rewrite_form_ ~rules f)
    in
    (* compute a basic set of rules *)
    let rules = m.Model.terms
      |> CCList.filter_map
        (function
          | FO.Term t, FO.Term u ->
              begin match FOBack.T.view u with
              | FO.App (id, []) -> Some (id, t) (* id --> t *)
              | _ -> None
              end
          | _ -> None
        )
      |> ID.Map.of_list
    in
    (* rewrite every term *)
    Model.map m ~f:(rewrite_ ~rules)

  (* read the result *)
  let read_res_ ~state s =
    match DSexp.next s.sexp with
    | `Ok (`Atom "unsat") ->
        Sol.Res.Unsat
    | `Ok (`Atom "sat") ->
        let m = get_model_ ~state s |> rewrite_model_ in
        Sol.Res.Sat m
    | `Ok (`Atom "unknown") ->
        Sol.Res.Timeout
    | `Ok (`List [`Atom "error"; `Atom s]) ->
        Sol.Res.Error s
    | `Ok sexp ->
        let msg = CCFormat.sprintf "@[unexpected answer from CVC4:@ %a@]"
          CCSexpM.print sexp
        in
        Sol.Res.Error msg
    | `Error e -> Sol.Res.Error e
    | `End -> Sol.Res.Error "no answer from the solver"

  let res t = match t.res with
    | Some r -> r
    | None ->
        let r =
          try read_res_ ~state:t.decode t
          with Error e -> Sol.Res.Error e
        in
        t.res <- Some r;
        r

  (* does two things:
      - add some dummy constants for non-parametrized types (for asking for
          the type's domain later)
      - compute the set of symbols for which we want the model's value *)
  let preprocess_pb_ pb =
    let n = ref 0 in
    FOI.Problem.fold_flat_map
      (fun acc stmt -> match stmt with
        | FOI.Decl (id,_) ->
            ID.Map.add id Q_const acc, [stmt]
        | FOI.TyDecl (id,0) ->
            (* add a dummy constant *)
            let c = ID.make ~name:(CCFormat.sprintf "__nun_card_witness_%d" !n) in
            incr n;
            let ty_c = [], FO_T.Ty.const id in
            let acc' = ID.Map.add c (Q_type id) acc in
            (* declare [c] *)
            acc', [stmt; FOI.Decl (c, ty_c)]
        | FOI.TyDecl _
        | FOI.Axiom _
        | FOI.Goal _
        | FOI.MutualTypes (_,_) -> acc, [stmt])
      ID.Map.empty
      pb

  let solve ?(timeout=30.) problem =
    let symbols, problem' = preprocess_pb_ problem in
    let s = create_ ~timeout ~symbols () in
    send_ s problem';
    s
end

(* solve problem using CVC4 before [deadline] *)
let call (type f)(type t)(type ty)
(module F : FO.S with type T.t=t and type formula=f and type Ty.t=ty)
~print ~print_smt ~deadline problem =
  let module FOBack = FO.Default in
  let module P = FO.Print(F) in
  let module Sol = Solver_intf in
  let module Res = Problem.Res in
  let module CVC4 = Make(F) in
  (* how much time remains *)
  let timeout = deadline -. Unix.gettimeofday() in
  if timeout < 0.1 then Problem.Res.Timeout
  else (
    if print
      then Format.printf "@[<v2>FO problem:@ %a@]@." P.print_problem problem;
    if print_smt
      then Format.printf "@[<v2>SMT problem:@ %a@]@." CVC4.print_problem problem;
    let solver = CVC4.solve ~timeout problem in
    match CVC4.res solver with
    | Sol.Res.Sat m -> Res.Sat m
    | Sol.Res.Unsat -> Res.Unsat
    | Sol.Res.Timeout -> Res.Timeout
    | Sol.Res.Error e ->
        failwith e
  )

(* close a pipeline with CVC4 *)
let close_pipe (type f)(type t)(type ty)
(module F : FO.S with type T.t=t and type formula=f and type Ty.t=ty)
~pipe ~print ~print_smt ~deadline
=
  let module FOBack = FO.Default in
  let module P = FO.Print(FOBack) in
  Transform.ClosedPipe.make1
    ~pipe
    ~f:(call (module F) ~deadline ~print ~print_smt)
