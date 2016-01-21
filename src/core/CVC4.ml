
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

type model_term = FO.Default.T.t
type model_ty = FO.Default.Ty.t

module DSexp = CCSexpM.MakeDecode(struct
  type 'a t = 'a
  let return x = x
  let (>>=) x f = f x
end)

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
  module P = FO.Print(FOBack)

  type problem = (FO_T.T.t, FO_T.Ty.t) FO.Problem.t

  type decoded_sym =
    | ID of id (* regular fun *)
    | DataTest of id
    | DataSelect of id * int

  type model_query =
    | Q_const
        (* we want to know the value of this constant *)
    | Q_fun of int
        (* we want to know the value of this function (int: arity) *)
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
    vars: FOBack.Ty.t Var.t ID.Tbl.t;
      (* variables in scope *)
  }

  let create_decode_state ~symbols = {
    id_to_name=ID.Tbl.create 32;
    decode_tbl=Hashtbl.create 32;
    symbols;
    vars=ID.Tbl.create 32;
  }

  (* the solver is dealt with through stdin/stdout *)
  type t = {
    oc : out_channel;
    fmt : Format.formatter; (* prints on [oc] *)
    ic : in_channel;
    decode: decode_state;
    mutable sexp : DSexp.t;
    mutable closed : bool;
    mutable res : (FOBack.T.t, FOBack.Ty.t) Sol.Res.t option;
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
      let name0 = match ID.name id, ID.polarity id with
        | s, Polarity.NoPol  -> s ^ "_" (* avoid clashes with CVC4 builtins *)
        | s, Polarity.Pos -> s ^ "_+"
        | s, Polarity.Neg -> s ^ "_-"
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
      | FOI.Mu _ -> Utils.not_implemented "cannot send MU-term to CVC4"
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
        fpf out "(@[<2>%s@ (@[%a@])@ (@[<hv>%a@])@])"
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
  let errorf_ fmt = CCFormat.ksprintf fmt ~f:error_

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
    | `Atom _ as t ->
        let id = parse_id_ ~state t in
        (* can be a constant or a variable, depending on scoping *)
        begin try FOBack.T.var (ID.Tbl.find state.vars id)
        with Not_found -> FOBack.T.const id
        end
    | `List [`Atom "LAMBDA"; `List bindings; body] ->
        (* lambda term *)
        let bindings = List.map (parse_var_ ~state) bindings in
        (* enter scope of variables *)
        within_scope ~state bindings
          (fun () ->
            let body = parse_term_ ~state body in
            List.fold_right FOBack.T.fun_ bindings body)
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
        within_scope ~state bindings
          (fun () ->
            let f = parse_term_ ~state f in
            List.fold_right FOBack.T.forall bindings f)
    | `List [`Atom "exists"; `List bindings; f] ->
        let bindings = List.map (parse_var_ ~state) bindings in
        within_scope ~state bindings
          (fun () ->
            let f = parse_term_ ~state f in
            List.fold_right FOBack.T.exists bindings f)
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

  and within_scope ~state bindings f =
    List.iter (fun v -> ID.Tbl.add state.vars (Var.id v) v) bindings;
    CCFun.finally
      ~f
      ~h:(fun () ->
        List.iter (fun v -> ID.Tbl.remove state.vars (Var.id v)) bindings)

  (* parse a function with [n] arguments *)
  let parse_fun_ ~state ~arity:n term =
    (* split [t] into [n]-ary function arguments and body *)
    let rec get_args t n =
      if n=0
      then [], t
      else match FOBack.T.view t with
      | FO.Fun (v, t') ->
          let vars, body = get_args t' (n-1) in
          v :: vars, body
      | _ -> errorf_ "expected %d-ary function,@ got `@[%a@]`" n P.print_term t
    in
    (* split [t] into a list of equations [var = t'] where [var in vars] *)
    let rec get_eqns ~vars t =
      let fail() =
        errorf_ "expected a test <var = term>@ with var among @[%a@],@ but got @[%a@]@]"
          (CCFormat.list Var.print_full) vars P.print_term t
      in
      match FOBack.T.view t with
      | FO.And l -> CCList.flat_map (get_eqns ~vars) l
      | FO.Eq (t1, t2) ->
          begin match FOBack.T.view t1, FOBack.T.view t2 with
            | FO.Var v, _ when List.exists (Var.equal v) vars ->
                [v, t2]
            | _, FO.Var v when List.exists (Var.equal v) vars ->
                [v, t1]
            | _ -> fail()
          end
      | _ -> fail()
    in
    (* convert [t] into a decision tree.
       [f] is applied to RHS terms *)
    let rec dt_of_body ~vars ~f t = match FOBack.T.view t with
      | FO.Ite (test, t1, t2) ->
          let eqns = get_eqns ~vars test in
          let t2 = dt_of_body ~vars ~f t2 in
          Model.DT.ite eqns (f t1) t2
      | FO.Not t ->
          (* boolean decision tree, this is the "else" branch; we can
             push the negation in every result *)
          dt_of_body ~vars ~f:(fun t -> FOBack.T.not_ (f t)) t
      | FO.And _ ->
          (* a boolean test! we might succeed in interpreting it as a test *)
          let t' = FOBack.T.(ite t true_ false_) in
          dt_of_body ~vars ~f t'
      | FO.Eq _ ->
          (* `a = b` becomes `if a=b then true else false` *)
          let eqns = get_eqns ~vars t in
          Model.DT.ite eqns (f FOBack.T.true_) (Model.DT.yield (f FOBack.T.false_))
      | _ -> Model.DT.yield (f t)
    in
    (* parse term, then convert into [vars -> decision-tree] *)
    let t = parse_term_ ~state term in
    let vars, body = get_args t n in
    let dt = dt_of_body ~vars ~f:CCFun.id body in
    vars, dt

  let sym_get_const_ ~state id = match ID.Map.find id state.symbols with
    | Q_const -> `Const
    | Q_fun n -> `Fun n
    | Q_type _ -> assert false

  let sym_get_ty_ ~state id = match ID.Map.find id state.symbols with
    | Q_const
    | Q_fun _ -> assert false
    | Q_type ty -> ty

  (* state: decode_state *)
  let parse_model_ ~state : CCSexp.t -> _ Model.t = function
    | `Atom _ -> error_ "expected model, got atom"
    | `List assoc ->
      (* parse model *)
      let m = List.fold_left
        (fun m -> function
          | `List [`Atom _ as s; term] ->
              (* regular constant, whose value we are interested in *)
              let id = parse_id_ ~state s in
              begin match sym_get_const_ ~state id with
              | `Const ->
                  let t = parse_term_ ~state term in
                  Model.add_const m (FOBack.T.const id, t)
              | `Fun n ->
                  let vars, t = parse_fun_ ~state ~arity:n term in
                  Model.add_fun m (FOBack.T.const id, vars, t)
              end
          | `List [`List [`Atom "fmf.card.val"; (`Atom _ as s)]; n] ->
              (* finite domain *)
              let id = parse_id_ ~state s in
              (* which type? *)
              let ty_id = sym_get_ty_ ~state id in
              let ty = FOBack.Ty.const ty_id in
              (* read cardinal *)
              let n = parse_int_ n in
              let terms = Sequence.(0 -- (n-1)
                |> map
                  (fun i ->
                    let name = CCFormat.sprintf "@uc_%a__%d" ID.print_name ty_id i in
                    let id = match find_atom_ ~state name with
                      | ID id -> id
                      | _ -> assert false
                    in
                    id)
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
      | Q_const
      | Q_fun _ -> pp_id out id
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
          List.length m.Model.constants
            + List.length m.Model.funs
            + List.length m.Model.finite_types
          =
          ID.Map.cardinal state.symbols
        in
        if not ok then error_ "some symbols are not defined in the model";
        m

  (* read the result *)
  let read_res_ ~state s =
    match DSexp.next s.sexp with
    | `Ok (`Atom "unsat") ->
        Utils.debug ~section 5 "CVC4 returned `unsat`";
        Sol.Res.Unsat
    | `Ok (`Atom "sat") ->
        Utils.debug ~section 5 "CVC4 returned `sat`";
        let m = if ID.Map.is_empty state.symbols
          then Model.empty
          else get_model_ ~state s
        in
        Sol.Res.Sat m
    | `Ok (`Atom "unknown") ->
        Utils.debug ~section 5 "CVC4 returned `unknown`";
        Sol.Res.Unknown
    | `Ok (`List [`Atom "error"; `Atom s]) ->
        Utils.debugf ~section 5 "@[<2>CVC4 returned `error %s`@]" (fun k->k s);
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
    FOI.Problem.fold_flat_map ~meta:(FO.Problem.meta pb)
      (fun acc stmt -> match stmt with
        | FOI.Decl (id,(args,_)) ->
            let len = List.length args in
            if len=0
            then ID.Map.add id Q_const acc, [stmt]
            else ID.Map.add id (Q_fun len) acc, [stmt]
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

  (* the command line to invoke CVC4 *)
  let mk_cvc4_cmd_ timeout options =
    Printf.sprintf
      "cvc4 --tlimit-per=%d --lang smt --finite-model-find \
       --uf-ss-fair-monotone %s"
      (int_of_float (timeout *. 1000.)) options

  let solve ?(options="") ?(timeout=30.) ?(print=false) problem =
    let symbols, problem' = preprocess_pb_ problem in
    if print
      then Format.printf "@[<v2>SMT problem:@ %a@]@." print_problem problem';
    if timeout < 0. then invalid_arg "CVC4.create: wrong timeout";
    let cmd = mk_cvc4_cmd_ timeout options in
    Utils.debugf ~section 2 "@[<2>run command@ `%s`@]" (fun k->k cmd);
    let ic, oc = Unix.open_process cmd in
    let s = create_ ~symbols (ic,oc) in
    send_ s problem';
    s

  exception Timeout

  let solve_par ?(j=3) ?(options=[""]) ?(timeout=30.) ?(print=false) problem =
    let unsat_means_unknown =
      problem.FO.Problem.meta.ProblemMetadata.unsat_means_unknown in
    let symbols, problem' = preprocess_pb_ problem in
    if print
      then Format.printf "@[<v2>SMT problem:@ %a@]@." print_problem problem';
    (* deadline: the instant we run out of time and must return *)
    let deadline = Unix.gettimeofday() +. timeout in
    let cmd options =
      let timeout = deadline -. Unix.gettimeofday() in
      if timeout < 0.1 then raise Timeout;
      mk_cvc4_cmd_ timeout options
    in
    let res = Scheduling.run options ~j ~cmd
      ~f:(fun cmd (ic,oc) ->
          (* the [t] instance *)
          let solver = create_ ~symbols (ic,oc) in
          send_ solver problem';
          let r = res solver in
          Utils.debugf ~section 3 "@[<2>result: %a@]" (fun k->k Sol.Res.pp r);
          match r with
          | Sol.Res.Sat m -> Scheduling.Return_shortcut (Sol.Res.Sat m)
          | Sol.Res.Unsat ->
              (* beware, this "unsat" might be wrong *)
              if unsat_means_unknown
              then Scheduling.Return Sol.Res.Unknown
              else Scheduling.Return_shortcut Sol.Res.Unsat
          | Sol.Res.Timeout
          | Sol.Res.Unknown -> Scheduling.Return r
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
          if List.mem Sol.Res.Unsat l then Sol.Res.Unsat
          else if List.mem Sol.Res.Timeout l then Sol.Res.Timeout
          else (
            assert (List.for_all ((=) Sol.Res.Unknown) l);
            Sol.Res.Unknown
          )
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
?(options=[""]) ?j ~print ~print_smt ~deadline problem =
  if options=[] then invalid_arg "CVC4.call: empty list of options";
  let module FOBack = FO.Default in
  let module P = FO.Print(F) in
  let module Sol = Solver_intf in
  let module Res = Problem.Res in
  let module CVC4 = Make(F) in
  if print
    then Format.printf "@[<v2>FO problem:@ %a@]@." P.print_problem problem;
  let timeout = deadline -. Unix.gettimeofday() in
  let res = CVC4.solve_par ?j ~options ~timeout ~print:print_smt problem in
  match res with
    | Sol.Res.Sat m -> Res.Sat m
    | Sol.Res.Unsat -> Res.Unsat
    | Sol.Res.Timeout -> Res.Timeout
    | Sol.Res.Unknown -> Res.Unknown
    | Sol.Res.Error e -> raise e

(* close a pipeline with CVC4 *)
let close_pipe (type t)(type ty)
(module F : FO.S with type T.t=t and type Ty.t=ty)
?options ?j ~pipe ~print ~print_smt ~deadline
=
  let module FOBack = FO.Default in
  let module P = FO.Print(FOBack) in
  Transform.ClosedPipe.make1
    ~pipe
    ~f:(call (module F) ?options ?j ~deadline ~print ~print_smt)
