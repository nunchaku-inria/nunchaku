
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Interface to CVC4} *)

module E = CCError
module Var = Var
module ID = ID
module Sol = Solver_intf
module FOI = FO

type id = ID.t

let section = Utils.Section.make "cvc4"

let fpf = Format.fprintf
let spf = CCFormat.sprintf

module DSexp = CCSexpM.MakeDecode(struct
  type 'a t = 'a
  let return x = x
  let (>>=) x f = f x
end)

type model_elt = FO.Default.T.t

exception CVC4_error of string

let () = Printexc.register_printer
  (function
    | CVC4_error msg -> Some (spf "@[CVC4 error:@ %s@]" msg)
    | _ -> None)

module Make(FO_T : FO.S) = struct
  module FO_T = FO_T
  module T = FO_T.T
  module Ty = FO_T.Ty

  (* for the model *)
  module FOBack = FO.Default

  type problem = (FO_T.T.t, FO_T.Ty.t) FO.Problem.t

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
    id_to_name: string ID.Tbl.t;
      (* maps ID to unique names *)
    decode_tbl: (string, decoded_sym) Hashtbl.t;
      (* map (stringof ID) -> ID, and other builtins *)
    symbols : model_query ID.Map.t;
      (* set of symbols to ask values for in the model *)
  }

  let create_decode_state ~symbols = {
    id_to_name=ID.Tbl.create 32;
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
      try
        Format.pp_print_flush s.fmt ();
        output_string s.oc "(exit)\n";
        flush s.oc;
        close_in_noerr s.ic;
        close_out_noerr s.oc;
        (* release buffer *)
        s.sexp <- DSexp.make ~bufsize:5 (fun _ _ _ -> assert false);
      with _ -> ()
    )

  (* TODO: use Scheduling instead *)

  let create_ ~symbols (ic,oc) =
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

  let pp_list ?(start="") ?(stop="") pp =
    CCFormat.list ~sep:" " ~start ~stop pp

  (* add numeric suffix to [name] until it is an unused name *)
  let find_unique_name_ ~state name0 =
    if not (Hashtbl.mem state.decode_tbl name0) then name0
    else (
      let n = ref 0 in
      while Hashtbl.mem state.decode_tbl (spf "%s_%d" name0 !n) do incr n done;
      spf "%s_%d" name0 !n
    )

  (* injection from ID to string *)
  let id_to_name ~state id =
    try ID.Tbl.find state.id_to_name id
    with Not_found ->
      let name0 = match ID.name id with
        | "distinct" -> "distinct_"
        | s -> s
      in
      let name = find_unique_name_ ~state name0 in
      Hashtbl.add state.decode_tbl name (ID id);
      ID.Tbl.add state.id_to_name id name;
      name

  (* print problems.
    @param state decode_state used for disambiguating symbols, and to
      be populated for later *)
  let print_problem_ ~state =
    (* print ID and remember its name for parsing model afterward *)
    let rec print_id out id =
      (* find a unique name for this ID *)
      let name = id_to_name ~state id in
      CCFormat.string out name

    (* print [is-c] for a constructor [c] *)
    and print_tester out c =
      let name = Printf.sprintf "is-%s" (id_to_name ~state c) in
      Hashtbl.replace state.decode_tbl name (DataTest c);
      CCFormat.string out name

    (* print [select-c-n] to select the n-th argument of [c] *)
    and print_select out (c,n) =
      let name = Printf.sprintf "_select_%s_%d" (id_to_name ~state c) n in
      Hashtbl.replace state.decode_tbl name (DataSelect (c,n));
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
      | FOI.Var v -> Var.print_full out v
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
            Var.print_full v print_ty (Var.ty v) print_term t
      | FOI.Let (v,t,u) ->
          fpf out "@[<3>(let@ ((%a %a))@ %a@])"
            Var.print_full v print_term t print_term u
      | FOI.Ite (a,b,c) ->
          fpf out "@[<2>(ite@ %a@ %a@ %a)@]"
            print_term a print_term b print_term c
      | FOI.True -> CCFormat.string out "true"
      | FOI.False -> CCFormat.string out "false"
      | FOI.Eq (a,b) -> fpf out "(@[=@ %a@ %a@])" print_term a print_term b
      | FOI.And [] -> CCFormat.string out "true"
      | FOI.And [f] -> print_term out f
      | FOI.And l ->
          fpf out "(@[and@ %a@])" (pp_list print_term) l
      | FOI.Or [] -> CCFormat.string out "false"
      | FOI.Or [f] -> print_term out f
      | FOI.Or l ->
          fpf out "(@[or@ %a@])" (pp_list print_term) l
      | FOI.Not f ->
          fpf out "(@[not@ %a@])" print_term f
      | FOI.Imply (a,b) ->
          fpf out "(@[=>@ %a@ %a@])" print_term a print_term b
      | FOI.Equiv (a,b) ->
          fpf out "(@[=@ %a@ %a@])" print_term a print_term b
      | FOI.Forall (v,f) ->
          fpf out "(@[<2>forall@ ((%a %a))@ %a@])"
            Var.print_full v print_ty (Var.ty v) print_term f
      | FOI.Exists (v,f) ->
          fpf out "(@[<2>exists@ ((%a %a))@ %a@])"
            Var.print_full v print_ty (Var.ty v) print_term f

    and print_statement out = function
      | FOI.TyDecl (id,arity) ->
          fpf out "(@[declare-sort@ %a@ %d@])" print_id id arity
      | FOI.Decl (v,ty) ->
          fpf out "(@[<2>declare-fun@ %a@ %a@])"
            print_id v print_ty_decl ty
      | FOI.Axiom t ->
          fpf out "(@[assert@ %a@])" print_term t
      | FOI.Goal t ->
          fpf out "(@[assert@ %a@])" print_term t
      | FOI.MutualTypes (k, l) ->
        let pp_arg out (c,i,ty) =
          fpf out "(@[<h>%a %a@])" print_select (c,i) print_ty ty in
        let pp_cstor out c =
          (* add selectors *)
          let args = List.mapi (fun i ty -> c.FOI.cstor_name,i,ty) c.FOI.cstor_args in
          fpf out "(@[<2>%a@ %a@])" print_id c.FOI.cstor_name
            (pp_list pp_arg) args
        in
        let print_tydef out tydef =
          fpf out "(@[<2>%a@ %a@])"
            print_id tydef.FOI.ty_name
            (pp_list pp_cstor) (ID.Map.to_list tydef.FOI.ty_cstors |> List.map snd)
        in
        fpf out "(@[<2>%s (%a) (%a)@])"
          (match k with `Data -> "declare-datatypes"
            | `Codata -> "declare-codatatypes")
          (pp_list print_id) l.FOI.tys_vars
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
    fpf s.fmt "%a@." (print_problem_ ~state:s.decode) problem;
    ()

  let print_problem out pb =
    let state = create_decode_state ~symbols:ID.Map.empty in
    print_problem_ ~state out pb

  let error_ e = raise (CVC4_error e)

  let find_atom_ ~state s =
    try Hashtbl.find state.decode_tbl s
    with Not_found ->
      (* introduced by CVC4 in the model; make a new ID *)
      let id = ID.make s in
      Hashtbl.replace state.decode_tbl s (ID id);
      ID id

  (* parse an identifier *)
  let parse_atom_ ~state = function
    | `Atom s -> find_atom_ ~state s
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

  let parse_int_ = function
    | `Atom n -> (try int_of_string n with _ -> error_ "expected int")
    | `List _ -> error_ "expected int"

  (* parse a ground term *)
  let rec parse_term_ ~state = function
    | `Atom "true" -> FOBack.T.true_
    | `Atom "false" -> FOBack.T.false_
    | `Atom _ as t -> FOBack.T.const (parse_id_ ~state t)
    | `List [`Atom "LAMBDA"; `List bindings; body] ->
        (* lambda term *)
        let bindings = List.map (parse_var_ ~state) bindings in
        let body = parse_term_ ~state body in
        List.fold_right FOBack.T.fun_ bindings body
    | `List [`Atom "ite"; a; b; c] ->
        let a = parse_term_ ~state a in
        let b = parse_term_ ~state b in
        let c = parse_term_ ~state c in
        FOBack.T.ite a b c
    | `List [`Atom "="; a; b] ->
        let a = parse_term_ ~state a in
        let b = parse_term_ ~state b in
        FOBack.T.eq a b
    | `List [`Atom "not"; f] ->
        let f = parse_term_ ~state f in
        FOBack.T.not_ f
    | `List (`Atom "and" :: l) ->
        FOBack.T.and_ (List.map (parse_term_ ~state) l)
    | `List (`Atom "or" :: l) ->
        FOBack.T.or_ (List.map (parse_term_ ~state) l)
    | `List [`Atom "forall"; `List bindings; f] ->
        let bindings = List.map (parse_var_ ~state) bindings in
        let f = parse_term_ ~state f in
        List.fold_right FOBack.T.forall bindings f
    | `List [`Atom "exists"; `List bindings; f] ->
        let bindings = List.map (parse_var_ ~state) bindings in
        let f = parse_term_ ~state f in
        List.fold_right FOBack.T.exists bindings f
    | `List [`Atom "=>"; a; b] ->
        let a = parse_term_ ~state a in
        let b = parse_term_ ~state b in
        FOBack.T.imply a b
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
              let t = parse_term_ ~state term in
              Model.add m (FOBack.T.const id, t)
          | `List [`List [`Atom "fmf.card.val"; (`Atom _ as s)]; n] ->
              (* finite domain *)
              let id = parse_id_ ~state s in
              (* which type? *)
              let ty_id = sym_get_ty_ ~state id in
              let ty = FOBack.T.const ty_id in
              (* read cardinal *)
              let n = parse_int_ n in
              let terms = Sequence.(0 -- (n-1)
                |> map
                  (fun i ->
                    let name = CCFormat.sprintf "@uc_%a_%d" ID.print_name ty_id i in
                    let id = match find_atom_ ~state name with
                      | ID id -> id
                      | _ -> assert false
                    in
                    FOBack.T.const id)
                |> to_rev_list
              ) in
              Model.add_finite_type m ty terms
          | _ -> error_ "expected pair key/value in the model")
        Model.empty
        assoc
      in
      m

  let send_get_model_ ~state out syms =
    (* print a single symbol *)
    let pp_id out i = CCFormat.string out (ID.Tbl.find state.id_to_name i) in
    let pp_mquery out (id, q) = match q with
      | Q_const -> pp_id out id
      | Q_type _ -> fpf out "(fmf.card.val %a)" pp_id id
    in
    fpf out "(@[<hv2>get-value@ (@[<hv>%a@])@])"
      (CCFormat.seq ~start:"" ~sep:" " ~stop:"" pp_mquery)
      (ID.Map.to_seq syms)

  (* read model from CVC4 instance [s] *)
  let get_model_ ~state s : _ Model.t =
    Utils.debugf ~section 3 "@[<2>ask for model with@ %a@]"
      (fun k -> k (send_get_model_ ~state) state.symbols);
    fpf s.fmt "%a@." (send_get_model_ ~state) state.symbols;
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
    (* compute a basic set of rules *)
    let rules = m.Model.terms
      |> CCList.filter_map
        (fun (t, u) ->
            match FOBack.T.view u with
            | FO.App (id, []) when CCString.prefix ~pre:"@uc_" (ID.name id) ->
                Some (id, t) (* id --> t *)
            | _ -> None)
      |> ID.Map.of_list
    in
    let pp_rule out (l,r) =
      let module P = FO.Print(FOBack) in
      fpf out "%a → @[%a@]" ID.print l P.print_term r
    in
    Utils.debugf 5 ~section "@[<2>apply rewrite rules@ @[<hv>%a@]@]"
      (fun k->k (CCFormat.seq ~start:"" ~stop:"" ~sep:"" pp_rule) (ID.Map.to_seq rules));
    (* rewrite [t] using the set of rewrite rules *)
    let rec rewrite_term_ t = match FOBack.T.view t with
      | FO.Builtin _
      | FO.Var _ -> t
      | FO.App (id,[]) ->
          begin try ID.Map.find id rules (* apply rule *)
          with Not_found -> t
          end
      | FO.DataTest(c,t) -> FOBack.T.data_test c (rewrite_term_ t)
      | FO.DataSelect(c,n,t) -> FOBack.T.data_select c n (rewrite_term_ t)
      | FO.Undefined _ -> assert false
      | FO.App (id, l) -> FOBack.T.app id (List.map rewrite_term_ l)
      | FO.Fun (v,t) ->
          (* no capture, rules rewrite to closed terms *)
          FOBack.T.fun_ v (rewrite_term_ t)
      | FO.Let (v,t,u) ->
          FOBack.T.let_ v (rewrite_term_ t) (rewrite_term_ u)
      | FO.Ite (a,b,c) ->
          FOBack.T.ite (rewrite_term_ a) (rewrite_term_ b) (rewrite_term_ c)
      | FO.True
      | FO.False -> t
      | FO.Eq (a,b) -> FOBack.T.eq (rewrite_term_ a) (rewrite_term_ b)
      | FO.And l -> FOBack.T.and_ (List.map (rewrite_term_) l)
      | FO.Or l -> FOBack.T.or_ (List.map (rewrite_term_) l)
      | FO.Not form -> FOBack.T.not_ (rewrite_term_ form)
      | FO.Imply (a,b) -> FOBack.T.imply (rewrite_term_ a)(rewrite_term_ b)
      | FO.Equiv (a,b) -> FOBack.T.equiv (rewrite_term_ a)(rewrite_term_ b)
      | FO.Forall (v,form) -> FOBack.T.forall v (rewrite_term_ form)
      | FO.Exists (v,form) -> FOBack.T.exists v (rewrite_term_ form)
    in
    (* rewrite every term *)
    Model.map m ~f:rewrite_term_

  (* read the result *)
  let read_res_ ~state s =
    match DSexp.next s.sexp with
    | `Ok (`Atom "unsat") ->
        Sol.Res.Unsat
    | `Ok (`Atom "sat") ->
        let m = if ID.Map.is_empty state.symbols
          then Model.empty
          else get_model_ ~state s |> rewrite_model_
        in
        Sol.Res.Sat m
    | `Ok (`Atom "unknown") ->
        Sol.Res.Timeout
    | `Ok (`List [`Atom "error"; `Atom s]) ->
        Sol.Res.Error (CVC4_error s)
    | `Ok sexp ->
        let msg = CCFormat.sprintf "@[unexpected answer from CVC4:@ %a@]"
          CCSexpM.print sexp
        in
        Sol.Res.Error (CVC4_error msg)
    | `Error e -> Sol.Res.Error (CVC4_error e)
    | `End -> Sol.Res.Error (CVC4_error "no answer from the solver")

  let res t = match t.res with
    | Some r -> r
    | None ->
        let r =
          try read_res_ ~state:t.decode t
          with e -> Sol.Res.Error e
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
            let c = ID.make (CCFormat.sprintf "__nun_card_witness_%d" !n) in
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

  let solve ?(options="") ?(timeout=30.) ?(print=false) problem =
    let symbols, problem' = preprocess_pb_ problem in
    if print
      then Format.printf "@[<v2>SMT problem:@ %a@]@." print_problem problem';
    if timeout < 0. then invalid_arg "CVC4.create: wrong timeout";
    let cmd = Printf.sprintf
      "cvc4 --tlimit-per=%d --lang smt --finite-model-find %s"
      (int_of_float (timeout *. 1000.)) options in
    Utils.debugf ~section 2 "@[<2>run command@ `%s`@]" (fun k->k cmd);
    let ic, oc = Unix.open_process cmd in
    let s = create_ ~symbols (ic,oc) in
    send_ s problem';
    s

  (* TODO some global parameter for [j] (default 3) *)

  exception Timeout

  let solve_par ?(j=3) ?(options=[""]) ?(timeout=30.) ?(print=false) problem =
    let symbols, problem' = preprocess_pb_ problem in
    if print
      then Format.printf "@[<v2>SMT problem:@ %a@]@." print_problem problem';
    (* deadline: the instant we run out of time and must return *)
    let deadline = Unix.gettimeofday() +. timeout in
    let cmd options =
      let timeout = deadline -. Unix.gettimeofday() in
      if timeout < 0.1 then raise Timeout;
      Printf.sprintf
        "cvc4 --tlimit-per=%d --lang smt --finite-model-find %s"
        (int_of_float (timeout *. 1000.)) options
    in
    let res = Scheduling.run options ~j ~cmd
      ~f:(fun cmd (ic,oc) ->
          (* the [t] instance *)
          let solver = create_ ~symbols (ic,oc) in
          send_ solver problem';
          match res solver with
          | Sol.Res.Sat m -> Scheduling.Return_shortcut (Sol.Res.Sat m)
          | Sol.Res.Unsat -> Scheduling.Return Sol.Res.Unsat
          | Sol.Res.Timeout -> Scheduling.Fail Timeout
          | Sol.Res.Error e ->
              Utils.debugf ~section 1
                "@[<2>error while running CVC4@ with `%s`:@ @[%s@]@]"
                (fun k->k cmd (Printexc.to_string e));
              raise e
        )
    in
    match res with
      | Scheduling.Return_shortcut x -> x
      | Scheduling.Return l ->
          assert (List.for_all ((=) Sol.Res.Unsat) l);
          Sol.Res.Unsat
      | Scheduling.Fail Timeout -> Sol.Res.Timeout
      | Scheduling.Fail e -> Sol.Res.Error e
end

let options_l =
  [ ""
  ; "--fmf-inst-engine"
  ; "--uf-ss=no-minimal"
  ; "--uf-ss=none"
  ; "--mbqi=none"
  ; "--mbqi=gen-ev"
  ; "--uf-ss-totality"
  ]

(* solve problem using CVC4 before [deadline] *)
let call (type t)(type ty)
(module F : FO.S with type T.t=t and type Ty.t=ty)
?(options=[""]) ~print ~print_smt ~deadline problem =
  if options=[] then invalid_arg "CVC4.call: empty list of options";
  let module FOBack = FO.Default in
  let module P = FO.Print(F) in
  let module Sol = Solver_intf in
  let module Res = Problem.Res in
  let module CVC4 = Make(F) in
  if print
    then Format.printf "@[<v2>FO problem:@ %a@]@." P.print_problem problem;
  let timeout = deadline -. Unix.gettimeofday() in
  let res = CVC4.solve_par ~options ~timeout ~print:print_smt problem in
  match res with
    | Sol.Res.Sat m -> Res.Sat m
    | Sol.Res.Unsat -> Res.Unsat
    | Sol.Res.Timeout -> Res.Timeout
    | Sol.Res.Error e -> raise e

(* close a pipeline with CVC4 *)
let close_pipe (type t)(type ty)
(module F : FO.S with type T.t=t and type Ty.t=ty)
?options ~pipe ~print ~print_smt ~deadline
=
  let module FOBack = FO.Default in
  let module P = FO.Print(FOBack) in
  Transform.ClosedPipe.make1
    ~pipe
    ~f:(call (module F) ?options ~deadline ~print ~print_smt)
