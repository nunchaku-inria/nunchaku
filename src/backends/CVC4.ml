
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Interface to CVC4} *)

open Nunchaku_core

module E = CCError
module Var = Var
module ID = ID
module FOI = FO
module Res = Problem.Res
module S = Scheduling

type id = ID.t

let name = "cvc4"
let section = Utils.Section.make name

let fpf = Format.fprintf

type model_term = FO.Default.T.t
type model_ty = FO.Default.Ty.t

module DSexp = CCSexpM.MakeDecode(struct
  type 'a t = 'a
  let return x = x
  let (>>=) x f = f x
end)

exception Error of string
exception CVC4_error of string

let error_ e = raise (Error e)
let errorf_ fmt = CCFormat.ksprintf fmt ~f:error_

let () = Printexc.register_printer
  (function
    | Error msg -> Some (Utils.err_sprintf "@[in the interface to CVC4:@ %s@]" msg)
    | CVC4_error msg -> Some (Utils.err_sprintf "@[in CVC4:@ %s@]" msg)
    | _ -> None)

(* TODO: simplify internals (no more "solver" type exposed, just a future)
   -> no explicit "close", use MVar *)

module Make(FO_T : FO.S) = struct
  module FO_T = FO_T
  module T = FO_T.T
  module Ty = FO_T.Ty

  (* for the model *)
  module FOBack = FO.Default
  module P = FO.Print(FOBack)

  type problem = (FO_T.T.t, FO_T.Ty.t) FO.Problem.t

  type symbol_kind = Model.symbol_kind

  type decoded_sym =
    | ID of id (* regular fun *)
    | DataTest of id
    | DataSelect of id * int

  (* a ground type, such as [to a (list b)] *)
  type ground_ty = Ty.t

  let gty_make = Ty.app
  let gty_const id = gty_make id []

  let rec gty_equal a b = match Ty.view a, Ty.view b with
    | FOI.TyBuiltin a, FOI.TyBuiltin b -> a=b
    | FOI.TyApp (hd_a, l_a), FOI.TyApp (hd_b, l_b) ->
        ID.equal hd_a hd_b
        && CCList.equal gty_equal l_a l_b
    | FOI.TyBuiltin _, _ | FOI.TyApp _, _ -> false

  type 'a gty_map = (ground_ty * 'a) list ID.Map.t

  let gty_map_empty : _ gty_map = ID.Map.empty

  let gty_head ty =
    match Ty.view ty with
      | FOI.TyApp (id,_) -> Some id
      | FOI.TyBuiltin _ -> None

  let gty_map_add m g x =
    match gty_head g with
    | None -> assert false
    | Some id ->
        let l = ID.Map.get_or id m ~or_:[] in
        if CCList.Assoc.mem ~eq:gty_equal l g
        then m
        else ID.Map.add id ((g,x) :: l) m

  let gty_map_find_exn m g =
    match gty_head g with
      | None -> raise Not_found
      | Some id ->
          let l = ID.Map.find id m in
          CCList.Assoc.get_exn ~eq:gty_equal l g

  let gty_map_mem m g = try ignore (gty_map_find_exn m g); true with Not_found -> false

  let rec fobackty_of_ground_ty g = match Ty.view g with
    | FOI.TyApp (id,l) ->
        FOBack.Ty.app id (List.map fobackty_of_ground_ty l)
    | FOI.TyBuiltin b -> FOBack.Ty.builtin b

  type model_query =
    | Q_const
        (* we want to know the value of this constant *)
    | Q_fun of int
        (* we want to know the value of this function (int: arity) *)
    | Q_type of ground_ty
        (* [id -> ty] means that [id : ty] is a dummy value, and we  want
           to know the finite domain of [ty] by asking [(fmf.card.val id)] *)

  type decode_state = {
    kinds: symbol_kind ID.Map.t;
      (* ID -> its kind *)
    id_to_name: string ID.Tbl.t;
      (* maps ID to unique names *)
    name_to_id: (string, decoded_sym) Hashtbl.t;
      (* map (stringof ID) -> ID, and other builtins *)
    symbols : model_query ID.Tbl.t;
      (* set of symbols to ask values for in the model *)
    vars: FOBack.Ty.t Var.t ID.Tbl.t;
      (* variables in scope *)
    mutable witnesses : ID.t gty_map;
      (* type -> witness of this type *)
  }

  let create_decode_state ~kinds () = {
    kinds;
    id_to_name=ID.Tbl.create 32;
    name_to_id=Hashtbl.create 32;
    symbols=ID.Tbl.create 32;
    vars=ID.Tbl.create 32;
    witnesses=gty_map_empty;
  }

  (* the solver is dealt with through stdin/stdout *)
  type t = {
    oc : out_channel;
    fmt : Format.formatter; (* prints on [oc] *)
    ic : in_channel;
    decode: decode_state;
    mutable sexp : DSexp.t;
    mutable closed : bool;
    mutable res : (FOBack.T.t, FOBack.Ty.t) Problem.Res.t option;
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

  let create_ ~decode (ic,oc) =
    (* the [t] instance *)
    let s = {
      oc;
      fmt=Format.formatter_of_out_channel oc;
      ic;
      decode;
      closed=false;
      sexp=DSexp.make ~bufsize:4_000 (input ic);
      res=None;
    } in
    Gc.finalise close s; (* close on finalize *)
    s

  let pp_list ?(sep=" ") ?(start="") ?(stop="") pp = CCFormat.list ~sep ~start ~stop pp

  (* add numeric suffix to [name] until it is an unused name *)
  let find_unique_name_ ~decode name0 =
    if not (Hashtbl.mem decode.name_to_id name0) then name0
    else (
      let n = ref 0 in
      while
        Hashtbl.mem decode.name_to_id (Printf.sprintf "%s_%d" name0 !n)
      do incr n
      done;
      Printf.sprintf "%s_%d" name0 !n
    )

  (* injection from ID to string *)
  let id_to_name ~decode id =
    try ID.Tbl.find decode.id_to_name id
    with Not_found ->
      let name0 = match ID.name id, ID.polarity id with
        | s, Polarity.NoPol  -> s ^ "_" (* avoid clashes with CVC4 builtins *)
        | s, Polarity.Pos -> s ^ "_+"
        | s, Polarity.Neg -> s ^ "_-"
      in
      let name = find_unique_name_ ~decode name0 in
      Hashtbl.add decode.name_to_id name (ID id);
      ID.Tbl.add decode.id_to_name id name;
      name

  let pp_builtin_cvc4 out = function
    | `Prop -> CCFormat.string out "Bool"

  (* print ground type using CVC4's escaping rules *)
  let rec pp_gty ~decode out g =
    let normalize_str =
      String.map
        (fun c -> match c with
           | 'a'..'z' | 'A'..'Z' | '0'..'9' -> c
           | _ -> '_')
    in
    match Ty.view g with
    | FOI.TyBuiltin b -> pp_builtin_cvc4 out b
    | FOI.TyApp (id, []) ->
        CCFormat.string out (id_to_name ~decode id |> normalize_str)
    | FOI.TyApp (id,l) ->
        fpf out "_%s_%a_" (id_to_name ~decode id |> normalize_str)
          (pp_list ~sep:"_" (pp_gty ~decode)) l

  (* print processed problem *)
  let print_problem out (decode, pb) =
    (* print ID and remember its name for parsing model afterward *)
    let rec print_id out id =
      (* find a unique name for this ID *)
      let name = id_to_name ~decode id in
      CCFormat.string out name

    (* print [is-c] for a constructor [c] *)
    and print_tester out c =
      let name = Printf.sprintf "is-%s" (id_to_name ~decode c) in
      Hashtbl.replace decode.name_to_id name (DataTest c);
      CCFormat.string out name

    (* print [select-c-n] to select the n-th argument of [c] *)
    and print_select out (c,n) =
      let name = Printf.sprintf "_select_%s_%d" (id_to_name ~decode c) n in
      Hashtbl.replace decode.name_to_id name (DataSelect (c,n));
      CCFormat.string out name

    (* print type (a monomorphic type) in SMT *)
    and print_ty out ty = match Ty.view ty with
      | FOI.TyBuiltin b -> pp_builtin_cvc4 out b
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
      | FOI.Undefined (_,t) -> print_term out t (* tailcall, probably *)
      | FOI.Unparsable _ -> errorf_ "cannot print `unparsable` in SMTlib"
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
      | FOI.CardBound (ty_id, which, n) ->
          let witness =
            try gty_map_find_exn decode.witnesses (gty_const ty_id)
            with Not_found ->
              errorf_ "no witness declared for cardinality bound on %a" ID.print ty_id
          in
          begin match which with
            | `Max -> fpf out "(@[assert (fmf.card %a %d)@])" print_id witness n
            | `Min -> fpf out "(@[assert (not (fmf.card %a %d))@])" print_id witness (n-1)
          end
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
    fpf s.fmt "%a@." print_problem (s.decode, problem);
    ()

  let find_atom_ ~decode s =
    try Hashtbl.find decode.name_to_id s
    with Not_found ->
      (* introduced by CVC4 in the model; make a new ID *)
      let id = ID.make s in
      Hashtbl.replace decode.name_to_id s (ID id);
      ID id

  (* parse an identifier *)
  let parse_atom_ ~decode = function
    | `Atom s -> find_atom_ ~decode s
    | _ -> error_ "expected ID, got a list"

  let parse_id_ ~decode s = match parse_atom_ ~decode s with
    | ID id -> id
    | DataTest _
    | DataSelect _ -> error_ "expected ID, got data test/select"

  (* parse an atomic type *)
  let rec parse_ty_ ~decode = function
    | `Atom _ as f ->
        let id = parse_id_ ~decode f in
        FOBack.Ty.const id
    | `List (`Atom _ as f :: l) ->
        let id = parse_id_ ~decode f in
        let l = List.map (parse_ty_ ~decode) l in
        FOBack.Ty.app id l
    | _ -> error_ "invalid type"

  let parse_var_ ~decode = function
    | `List [`Atom _ as v; ty] ->
        let id = parse_id_ ~decode v in
        let ty = parse_ty_ ~decode ty in
        Var.of_id ~ty id
    | _ -> error_ "expected typed variable"

  let parse_int_ = function
    | `Atom n -> (try int_of_string n with _ -> error_ "expected int")
    | `List _ -> error_ "expected int"

  (* parse a ground term *)
  let rec parse_term_ ~decode = function
    | `Atom "true" -> FOBack.T.true_
    | `Atom "false" -> FOBack.T.false_
    | `Atom _ as t ->
        let id = parse_id_ ~decode t in
        (* can be a constant or a variable, depending on scoping *)
        begin try FOBack.T.var (ID.Tbl.find decode.vars id)
        with Not_found -> FOBack.T.const id
        end
    | `List [`Atom "LAMBDA"; `List bindings; body] ->
        (* lambda term *)
        let bindings = List.map (parse_var_ ~decode) bindings in
        (* enter scope of variables *)
        within_scope ~decode bindings
          (fun () ->
            let body = parse_term_ ~decode body in
            List.fold_right FOBack.T.fun_ bindings body)
    | `List [`Atom "ite"; a; b; c] ->
        let a = parse_term_ ~decode a in
        let b = parse_term_ ~decode b in
        let c = parse_term_ ~decode c in
        FOBack.T.ite a b c
    | `List [`Atom "="; a; b] ->
        let a = parse_term_ ~decode a in
        let b = parse_term_ ~decode b in
        FOBack.T.eq a b
    | `List [`Atom "not"; f] ->
        let f = parse_term_ ~decode f in
        FOBack.T.not_ f
    | `List (`Atom "and" :: l) ->
        FOBack.T.and_ (List.map (parse_term_ ~decode) l)
    | `List (`Atom "or" :: l) ->
        FOBack.T.or_ (List.map (parse_term_ ~decode) l)
    | `List [`Atom "forall"; `List bindings; f] ->
        let bindings = List.map (parse_var_ ~decode) bindings in
        within_scope ~decode bindings
          (fun () ->
            let f = parse_term_ ~decode f in
            List.fold_right FOBack.T.forall bindings f)
    | `List [`Atom "exists"; `List bindings; f] ->
        let bindings = List.map (parse_var_ ~decode) bindings in
        within_scope ~decode bindings
          (fun () ->
            let f = parse_term_ ~decode f in
            List.fold_right FOBack.T.exists bindings f)
    | `List [`Atom "=>"; a; b] ->
        let a = parse_term_ ~decode a in
        let b = parse_term_ ~decode b in
        FOBack.T.imply a b
    | `List (`Atom _ as f :: l) ->
        begin match parse_atom_ ~decode f, l with
          | ID f, _ ->
              (* regular function app *)
              let l = List.map (parse_term_ ~decode) l in
              FOBack.T.app f l
          | DataTest c, [t] ->
              let t = parse_term_ ~decode t in
              FOBack.T.data_test c t
          | DataTest _, _ -> error_ "invalid arity for DataTest"
          | DataSelect (c,n), [t] ->
              let t = parse_term_ ~decode t in
              FOBack.T.data_select c n t
          | DataSelect _, _ -> error_ "invalid arity for DataSelect"
        end
    | `List (`List _ :: _) -> error_ "non first-order list"
    | `List [] -> error_ "expected term, got empty list"

  and within_scope ~decode bindings f =
    List.iter (fun v -> ID.Tbl.add decode.vars (Var.id v) v) bindings;
    CCFun.finally
      ~f
      ~h:(fun () ->
        List.iter (fun v -> ID.Tbl.remove decode.vars (Var.id v)) bindings)

  (* parse a function with [n] arguments *)
  let parse_fun_ ~decode ~arity:n term =
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
    (* parse term, then convert into [vars -> decision-tree] *)
    let t = parse_term_ ~decode term in
    let vars, body = get_args t n in
    (* change the shape of [body] so it looks more like a decision tree *)
    let module U = FO.Util(FOBack) in
    let dt = U.dt_of_term ~vars body in
    Utils.debugf ~section 5 "@[<2>turn term `@[%a@]`@ into DT `@[%a@]`@]"
      (fun k->k P.print_term body (Model.DT.print P.print_term) dt);
    vars, dt

  let sym_get_const_ ~decode id = match ID.Tbl.find decode.symbols id with
    | Q_const -> `Const
    | Q_fun n -> `Fun n
    | Q_type _ -> assert false

  let sym_get_ty_ ~decode id = match ID.Tbl.find decode.symbols id with
    | Q_const
    | Q_fun _ -> assert false
    | Q_type ty -> ty

  let get_kind ~decode id =
    try ID.Map.find id decode.kinds
    with Not_found ->
      errorf_ "could not find kind of %a" ID.print id

  (* state: decode_state *)
  let parse_model_ ~decode : CCSexp.t -> _ Model.t = function
    | `Atom _ -> error_ "expected model, got atom"
    | `List assoc ->
      (* parse model *)
      let m = List.fold_left
        (fun m -> function
          | `List [`Atom _ as s; term] ->
              (* regular constant, whose value we are interested in *)
              let id = parse_id_ ~decode s in
              let kind = get_kind ~decode id in
              begin match sym_get_const_ ~decode id with
              | `Const ->
                  let t = parse_term_ ~decode term in
                  Model.add_const m (FOBack.T.const id, t, kind)
              | `Fun n ->
                  let vars, t = parse_fun_ ~decode ~arity:n term in
                  Model.add_fun m (FOBack.T.const id, vars, t, kind)
              end
          | `List [`List [`Atom "fmf.card.val"; (`Atom _ as s)]; n] ->
              (* finite domain *)
              let id = parse_id_ ~decode s in
              (* which type? *)
              let gty = sym_get_ty_ ~decode id in
              let ty = fobackty_of_ground_ty gty in
              (* read cardinal *)
              let n = parse_int_ n in
              let terms = Sequence.(0 -- (n-1)
                |> map
                  (fun i ->
                    let name =
                      CCFormat.sprintf "@[<h>@uc_%a_%d@]" (pp_gty ~decode) gty i in
                    let id = match find_atom_ ~decode name with
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

  let send_get_model_ out decode =
    (* print a single symbol *)
    let pp_id out i = CCFormat.string out (ID.Tbl.find decode.id_to_name i) in
    let pp_mquery out (id, q) = match q with
      | Q_const
      | Q_fun _ -> pp_id out id
      | Q_type _ -> fpf out "(fmf.card.val %a)" pp_id id
    in
    fpf out "(@[<hv2>get-value@ (@[<hv>%a@])@])"
      (CCFormat.seq ~start:"" ~sep:" " ~stop:"" pp_mquery)
      (ID.Tbl.to_seq decode.symbols)

  (* read model from CVC4 instance [s] *)
  let get_model_ ~decode s : _ Model.t =
    Utils.debugf ~section 3 "@[<2>ask for model with@ %a@]"
      (fun k -> k send_get_model_ decode);
    fpf s.fmt "%a@." send_get_model_ decode;
    (* read result back *)
    match DSexp.next s.sexp with
    | `Error e -> error_ e
    | `End -> error_ "unexpected end of input from CVC4: expected model"
    | `Ok sexp ->
        if !Solver_intf.print_model_
          then Format.eprintf "@[raw model:@ @[<hv>%a@]@]@." CCSexpM.print sexp;
        let m = parse_model_ ~decode sexp in
        (* check all symbols are defined *)
        let ok =
          List.length m.Model.constants
            + List.length m.Model.funs
            + List.length m.Model.finite_types
          =
          ID.Tbl.length decode.symbols
        in
        if not ok then error_ "some symbols are not defined in the model";
        m

  (* read the result *)
  let read_res_ ~decode s =
    match DSexp.next s.sexp with
    | `Ok (`Atom "unsat") ->
        Utils.debug ~section 5 "CVC4 returned `unsat`";
        Res.Unsat
    | `Ok (`Atom "sat") ->
        Utils.debug ~section 5 "CVC4 returned `sat`";
        let m = if ID.Tbl.length decode.symbols = 0
          then Model.empty
          else get_model_ ~decode s
        in
        Res.Sat m
    | `Ok (`Atom "unknown") ->
        Utils.debug ~section 5 "CVC4 returned `unknown`";
        Res.Unknown
    | `Ok (`List [`Atom "error"; `Atom s]) ->
        Utils.debugf ~section 5 "@[<2>CVC4 returned `error %s`@]" (fun k->k s);
        Res.Error (CVC4_error s)
    | `Ok sexp ->
        let msg = CCFormat.sprintf "@[unexpected answer from CVC4:@ %a@]"
          CCSexpM.print sexp
        in
        Res.Error (Error msg)
    | `Error e -> Res.Error (Error e)
    | `End -> Res.Error (Error "no answer from the solver")

  let res t = match t.res with
    | Some r -> r
    | None ->
        let r =
          try read_res_ ~decode:t.decode t
          with e -> Res.Error e
        in
        t.res <- Some r;
        r

  (* once processed, the problem also contains the set of symbols to
     read back from the model, and type witnesses *)
  type processed_problem = decode_state * problem

  (* is [ty] a finite (uninterpreted) type? *)
  let is_finite_ decode ty = match Ty.view ty with
    | FOI.TyApp (id, _) ->
        begin match get_kind ~decode id with
          | Model.Symbol_utype -> true
          | Model.Symbol_data | Model.Symbol_fun | Model.Symbol_prop -> false
        end
    | _ -> false

  (* does two things:
      - add some dummy constants for uninterpreted types (for asking for
          the type's domain later)
      - compute the set of symbols for which we want the model's value *)
  let preprocess pb : processed_problem =
    let module U = FO.Util(FO_T) in
    let kinds = U.problem_kinds pb in
    let n = ref 0 in
    let state = create_decode_state ~kinds () in
    let decl state id c = ID.Tbl.add state.symbols id c in
    (* if some types in [l] do not have a witness, add them to [[stmt]] *)
    let add_ty_witnesses stmt l =
      List.fold_left
        (fun acc gty ->
          if not (is_finite_ state gty) || gty_map_mem state.witnesses gty
          then acc (* already declared a witness for [gty], or [gty] is not
                      a finite type *)
          else (
            (* add a dummy constant *)
            let c = ID.make (CCFormat.sprintf "__nun_card_witness_%d" !n) in
            incr n;
            (* declare [c] *)
            let ty_c = [], gty in
            decl state c (Q_type gty);
            state.witnesses <- gty_map_add state.witnesses gty c;
            FOI.Decl (c, ty_c) :: acc
          ))
        [stmt] l
      |> List.rev
    in
    let pb =
      FOI.Problem.flat_map ~meta:(FO.Problem.meta pb)
      (fun stmt -> match stmt with
        | FOI.Decl (id,(args,_)) ->
            let len = List.length args in
            begin if len=0
              then decl state id Q_const
              else decl state id (Q_fun len)
            end;
            (* if args contains composite types, add witnesses for them *)
            add_ty_witnesses stmt args
        | FOI.CardBound (id,_,_)
        | FOI.TyDecl (id,0) ->
            add_ty_witnesses stmt [gty_const id]
        | FOI.TyDecl _
        | FOI.Axiom _
        | FOI.Goal _
        | FOI.MutualTypes (_,_) -> [stmt])
      pb
    in
    state, pb

  (* the command line to invoke CVC4 *)
  let mk_cvc4_cmd_ timeout options =
    let timeout_hard = int_of_float (timeout +. 2.) in
    let timeout_ms = int_of_float (timeout *. 1000.) in
    Printf.sprintf
      "ulimit -t %d; exec cvc4 --tlimit-per=%d --lang smt --finite-model-find \
       --uf-ss-fair-monotone --no-condense-function-values %s"
      timeout_hard timeout_ms options

  let do_solve_ options deadline print pb =
    let now = Unix.gettimeofday() in
    let deadline = match deadline with Some s -> s | None -> now +. 30. in
    (* preprocess first *)
    let decode, problem' = preprocess pb in
    if print
    then Format.printf "@[<v2>SMT problem:@ %a@]@." print_problem (decode, problem');
    (* enough time remaining? *)
    if now +. 0.1 > deadline
    then Res.Timeout, S.No_shortcut
    else (
      let timeout = deadline -. now in
      assert (timeout > 0.);
      let cmd = mk_cvc4_cmd_ timeout options in
      Utils.debugf ~lock:true ~section 2 "@[<2>run command@ `%s`@]" (fun k->k cmd);
      let ic, oc = Unix.open_process cmd in
      let s = create_ ~decode (ic,oc) in
      send_ s problem';
      let r = res s in
      Utils.debugf ~lock:true ~section 3 "@[<2>result: %a@]"
        (fun k->k (Res.print P.print_term P.print_ty) r);
      match r with
        | Res.Sat _ -> r, S.Shortcut
        | Res.Unsat ->
          (* beware, this "unsat" might be wrong *)
          if pb.FO.Problem.meta.ProblemMetadata.unsat_means_unknown
          then Res.Unknown, S.No_shortcut
          else Res.Unsat, S.Shortcut
        | Res.Timeout
        | Res.Unknown -> r, S.No_shortcut
        | Res.Error e ->
          Utils.debugf ~lock:true ~section 1
            "@[<2>error while running CVC4@ with `%s`:@ @[%s@]@]"
            (fun k->k cmd (Printexc.to_string e));
          raise e
    )

  let solve ?(options="") ?deadline ?(print=false) pb =
    S.Fut.make
      (fun () -> do_solve_ options deadline print pb)
end

let is_available () =
  try
    let res = Sys.command "which cvc4" = 0 in
    if res then Utils.debug ~section 3 "CVC4 is available";
    res
  with Sys_error _ -> false

let options_l =
  [ ""
  ; "--fmf-inst-engine"
  ; "--uf-ss=no-minimal --decision=internal"
  ; "--uf-ss=none"
  ; "--mbqi=none"
  ; "--mbqi=gen-ev"
  ; "--uf-ss-totality"
  ]

(* solve problem using CVC4 before [deadline] *)
let call (type t)(type ty)
(module F : FO.S with type T.t=t and type Ty.t=ty)
?(options="") ?deadline ?prio ~print ~print_smt problem
  =
  let module FOBack = FO.Default in
  let module P = FO.Print(F) in
  let module Res = Problem.Res in
  let module CVC4 = Make(F) in
  if print
  then Format.printf "@[<v2>FO problem:@ %a@]@." P.print_problem problem;
  Scheduling.Task.of_fut ?prio
    (fun () -> CVC4.solve ~options ?deadline ~print:print_smt problem)

let pipes fo ?(options=[""]) ?deadline ~print ~print_smt () =
  let encode pb =
    List.mapi
      (fun i options ->
         (* only print for the first task *)
         let print = print && i=0 in
         let print_smt = print_smt && i=0 in
         let prio = 30 + 10 * i in
         call fo ~options ?deadline ~prio ~print ~print_smt pb)
    options, ()
  in
  Transform.make ~name ~encode ~decode:(fun _ x -> x) ()

