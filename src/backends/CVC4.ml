
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Interface to CVC4} *)

open Nunchaku_core

module E = CCResult
module Res = Problem.Res
module S = Scheduling

type id = ID.t

let name = "cvc4"
let section = Utils.Section.make name

let fpf = Format.fprintf

type model_term = FO.T.t
type model_ty = FO.Ty.t

module DSexp = Sexp_lib.Decoder

exception Error of string
exception Backend_err of string

let error_ e = raise (Error e)
let errorf_ fmt = CCFormat.ksprintf fmt ~f:error_

let cvc4_error_ msg = raise (Backend_err msg)
let cvc4_errorf_ msg = CCFormat.ksprintf ~f:cvc4_error_ "@[in CVC4:@ %s@]" msg

let () = Printexc.register_printer
    (function
      | Error msg -> Some (Utils.err_sprintf "@[in the interface to CVC4:@ %s@]" msg)
      | _ -> None)

module T = FO.T
module Ty = FO.Ty

type problem = (T.t, Ty.t) FO.Problem.t

type symbol_kind = Model.symbol_kind

type decoded_sym =
  | ID of id (* regular fun *)
  | De_bruijn of int * Ty.t (* index to mu-binder *)
  | DataTest of id
  | DataSelect of id * int

(* a ground type, such as [to a (list b)] *)
type ground_ty = Ty.t

let gty_make = Ty.app
let gty_const id = gty_make id []

module GTy_map = CCMap.Make(FO.Ty)

let gty_head ty = match Ty.view ty with
  | FO.TyApp (id,_) -> Some id
  | FO.TyBuiltin _ -> None

let rec fobackty_of_ground_ty g = match Ty.view g with
  | FO.TyApp (id,l) ->
    Ty.app id (List.map fobackty_of_ground_ty l)
  | FO.TyBuiltin b -> Ty.builtin b

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
  vars: Ty.t Var.t ID.Tbl.t;
  (* variables in scope *)
  db_prefixes: (string,ground_ty) Hashtbl.t;
  (* prefixes expected for De Bruijn indices *)
  timer: Utils.Time.timer;
  (* time elapsed *)
  mutable db_stack: Ty.t Var.t option ref list;
  (* stack of variables for mu-binders, with a bool ref.
     If the ref is true, it means the variable is used at least once *)
  mutable witnesses : ID.t GTy_map.t;
  (* type -> witness of this type *)
}

let create_decode_state ~kinds () = {
  kinds;
  id_to_name=ID.Tbl.create 32;
  name_to_id=Hashtbl.create 32;
  symbols=ID.Tbl.create 32;
  db_prefixes=Hashtbl.create 8;
  db_stack=[];
  timer=Utils.Time.start_timer();
  vars=ID.Tbl.create 32;
  witnesses=GTy_map.empty;
}

(* the solver is dealt with through stdin/stdout *)
type t = {
  oc : out_channel;
  fmt : Format.formatter; (* prints on [oc] *)
  ic : in_channel;
  decode: decode_state;
  print_model: bool;
  options: string;
  mutable sexp : DSexp.t;
  mutable closed : bool;
  mutable res : (T.t, Ty.t) Problem.Res.t option;
}

let name = "cvc4"

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
    with _ -> ()
  )

let create_ ~options ~print_model ~decode (ic,oc) =
  (* the [t] instance *)
  let s = {
    oc;
    fmt=Format.formatter_of_out_channel oc;
    ic;
    options;
    print_model;
    decode;
    closed=false;
    sexp=DSexp.of_lexbuf (Lexing.from_channel ic);
    res=None;
  } in
  Gc.finalise close s; (* close on finalize *)
  s

let pp_list ?(sep=" ") pp = Utils.pp_list ~sep pp

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
  | `Unitype -> assert false
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
    | FO.TyBuiltin b -> pp_builtin_cvc4 out b
    | FO.TyApp (id, []) ->
      CCFormat.string out (id_to_name ~decode id |> normalize_str)
    | FO.TyApp (id,l) ->
      fpf out "_%s_%a_" (id_to_name ~decode id |> normalize_str)
        (pp_list ~sep:"_" (pp_gty ~decode)) l

(* the prefix used by CVC4 for constants of the given type *)
let const_of_ty ~decode gty =
  CCFormat.sprintf "@[<h>@@uc_%a@]" (pp_gty ~decode) gty

(* the i-th constant of the given type *)
let const_of_ty_nth ~decode gty i =
  CCFormat.sprintf "@[<h>%s_%d@]" (const_of_ty ~decode gty) i

let get_ty_witness ~decode gty =
  try GTy_map.find gty decode.witnesses
  with Not_found ->
    errorf_ "no witness declared for cardinality bound on %a" (pp_gty ~decode) gty

(* print processed problem *)
let pp_problem out (decode, pb) =
  (* print ID and remember its name for parsing model afterward *)
  let rec pp_id out id =
    (* find a unique name for this ID *)
    let name = id_to_name ~decode id in
    CCFormat.string out name

  (* print [is-c] for a constructor [c] *)
  and pp_tester out c =
    let name = Printf.sprintf "is-%s" (id_to_name ~decode c) in
    Hashtbl.replace decode.name_to_id name (DataTest c);
    CCFormat.string out name

  (* print [select-c-n] to select the n-th argument of [c] *)
  and pp_select out (c,n) =
    let name = Printf.sprintf "_select_%s_%d" (id_to_name ~decode c) n in
    Hashtbl.replace decode.name_to_id name (DataSelect (c,n));
    CCFormat.string out name

  (* print type (a monomorphic type) in SMT *)
  and pp_ty out ty = match Ty.view ty with
    | FO.TyBuiltin b -> pp_builtin_cvc4 out b
    | FO.TyApp (f, []) -> pp_id out f
    | FO.TyApp (f, l) ->
      fpf out "@[(%a@ %a)@]"
        pp_id f (pp_list pp_ty) l

  (* print type in SMT syntax *)
  and pp_ty_decl out ty =
    let args, ret = ty in
    fpf out "%a %a" (CCFormat.within "(" ")" (pp_list pp_ty)) args pp_ty ret

  and pp_term out t = match T.view t with
    | FO.Builtin b ->
      begin match b with
        | `Int n -> CCFormat.int out n
      end
    | FO.Var v -> Var.pp_full out v
    | FO.App (f,[]) -> pp_id out f
    | FO.App (f,l) ->
      fpf out "(@[%a@ %a@])"
        pp_id f (pp_list pp_term) l
    | FO.DataTest (c,t) ->
      fpf out "(@[%a@ %a@])" pp_tester c pp_term t
    | FO.DataSelect (c,n,t) ->
      fpf out "(@[%a@ %a@])" pp_select (c,n) pp_term t
    | FO.Undefined t -> pp_term out t (* tailcall, probably *)
    | FO.Undefined_atom _ -> errorf_ "cannot print `undefined_atom` in SMTlib"
    | FO.Unparsable _ -> errorf_ "cannot print `unparsable` in SMTlib"
    | FO.Card_at_least (_,n) when n <= 1 -> fpf out "true" (* trivial *)
    | FO.Card_at_least (ty,n) ->
      let witness = get_ty_witness ~decode ty in
      fpf out "(@[(not (fmf.card %a %d))@])" pp_id witness (n-1)
    | FO.Fun (v,t) ->
      fpf out "@[<3>(LAMBDA@ ((%a %a))@ %a)@]"
        Var.pp_full v pp_ty (Var.ty v) pp_term t
    | FO.Let (v,t,u) ->
      fpf out "@[<3>(let@ ((%a %a))@ %a@])"
        Var.pp_full v pp_term t pp_term u
    | FO.Mu _ -> Utils.not_implemented "cannot send MU-term to CVC4"
    | FO.Ite (a,b,c) ->
      fpf out "@[<2>(ite@ %a@ %a@ %a)@]"
        pp_term a pp_term b pp_term c
    | FO.True -> CCFormat.string out "true"
    | FO.False -> CCFormat.string out "false"
    | FO.Eq (a,b) -> fpf out "(@[=@ %a@ %a@])" pp_term a pp_term b
    | FO.And [] -> CCFormat.string out "true"
    | FO.And [f] -> pp_term out f
    | FO.And l ->
      fpf out "(@[and@ %a@])" (pp_list pp_term) l
    | FO.Or [] -> CCFormat.string out "false"
    | FO.Or [f] -> pp_term out f
    | FO.Or l ->
      fpf out "(@[or@ %a@])" (pp_list pp_term) l
    | FO.Not f ->
      fpf out "(@[not@ %a@])" pp_term f
    | FO.Imply (a,b) ->
      fpf out "(@[=>@ %a@ %a@])" pp_term a pp_term b
    | FO.Equiv (a,b) ->
      fpf out "(@[=@ %a@ %a@])" pp_term a pp_term b
    | FO.Forall (v,f) ->
      fpf out "(@[<2>forall@ ((%a %a))@ %a@])"
        Var.pp_full v pp_ty (Var.ty v) pp_term f
    | FO.Exists (v,f) ->
      fpf out "(@[<2>exists@ ((%a %a))@ %a@])"
        Var.pp_full v pp_ty (Var.ty v) pp_term f

  and pp_statement out = function
    | FO.TyDecl (id,arity,_) ->
      fpf out "(@[declare-sort@ %a@ %d@])" pp_id id arity
    | FO.Decl (v,ty,_) ->
      fpf out "(@[<2>declare-fun@ %a@ %a@])"
        pp_id v pp_ty_decl ty
    | FO.Axiom t ->
      fpf out "(@[assert@ %a@])" pp_term t
    | FO.Goal t ->
      fpf out "(@[assert@ %a@])" pp_term t
    | FO.CardBound (ty_id, which, n) ->
      let witness = get_ty_witness ~decode (gty_const ty_id) in
      let pp_max_card out n =
        if n < 1 then fpf out "(assert false)" (* absurd *)
        else fpf out "(@[assert (fmf.card %a %d)@])" pp_id witness n
      and pp_min_card out n =
        if n<=1 then ()
        else fpf out "(@[assert (not (fmf.card %a %d))@])" pp_id witness (n-1)
      in
      begin match which with
        | `Max -> pp_max_card out n
        | `Min -> pp_min_card out n
      end
    | FO.MutualTypes (k, l) ->
      let pp_arg out (c,i,ty) =
        fpf out "(@[<h>%a %a@])" pp_select (c,i) pp_ty ty in
      let pp_cstor out c =
        (* add selectors *)
        let args = List.mapi (fun i ty -> c.FO.cstor_name,i,ty) c.FO.cstor_args in
        fpf out "(@[<2>%a@ %a@])" pp_id c.FO.cstor_name
          (pp_list pp_arg) args
      in
      let pp_tydef out tydef =
        fpf out "(@[<2>%a@ %a@])"
          pp_id tydef.FO.ty_name
          (pp_list pp_cstor) (ID.Map.to_list tydef.FO.ty_cstors |> List.map snd)
      in
      fpf out "(@[<2>%s@ (@[%a@])@ (@[<hv>%a@])@])"
        (match k with `Data -> "declare-datatypes"
                    | `Codata -> "declare-codatatypes")
        (pp_list pp_id) l.FO.tys_vars
        (pp_list pp_tydef) l.FO.tys_defs

  in
  (* send prelude *)
  fpf out "@[<v>";
  fpf out "(set-option :produce-models true)@,";
  fpf out "(set-option :interactive-mode true)@,";
  fpf out "(set-logic ALL_SUPPORTED)@,"; (* taïaut! *)
  (* write problem *)
  Utils.pp_seq ~sep:""
    pp_statement out (CCVector.to_seq pb.FO.Problem.statements);
  fpf out "@,(check-sat)@]@.";
  ()

let send_ s problem =
  fpf s.fmt "%a@." pp_problem (s.decode, problem);
  Format.pp_print_flush s.fmt ();
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
  | `Atom s ->
    begin match CCString.Split.right ~by:"_" s with
      | None -> find_atom_ ~decode s
      | Some (pre,n) ->
        (* might be a De Bruijn index *)
        try
          let ty = Hashtbl.find decode.db_prefixes pre in
          let n = int_of_string n in
          De_bruijn (n,ty)
        with Not_found ->
          find_atom_ ~decode s
    end
  | _ -> error_ "expected ID, got a list"

let parse_id_ ~decode s = match parse_atom_ ~decode s with
  | ID id -> id
  | De_bruijn _
  | DataTest _
  | DataSelect _ -> error_ "expected ID, got data test/select/de bruijn"

(* parse an atomic type *)
let rec parse_ty_ ~decode = function
  | `Atom "Bool" -> Ty.builtin `Prop
  | `Atom _ as f ->
    let id = parse_id_ ~decode f in
    Ty.const id
  | `List (`Atom _ as f :: l) ->
    let id = parse_id_ ~decode f in
    let l = List.map (parse_ty_ ~decode) l in
    Ty.app id l
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
let rec parse_term_ ~decode s =
  let r = ref None in (* maybe, a mu-variable *)
  decode.db_stack <- r :: decode.db_stack;
  let res =
    CCFun.finally
      ~h:(fun () -> decode.db_stack <- List.tl decode.db_stack)
      ~f:(fun () -> parse_term_sub_ ~decode s)
  in
  match !r with
    | None -> res
    | Some v -> T.mu v res (* introduce a mu binder *)
and parse_term_sub_ ~decode = function
  | `Atom "true" -> T.true_
  | `Atom "false" -> T.false_
  | `Atom _ as t ->
    begin match parse_atom_ ~decode t with
      | ID id ->
        (* can be a constant or a variable, depending on scoping *)
        begin try T.var (ID.Tbl.find decode.vars id)
          with Not_found -> T.const id
        end
      | De_bruijn (n,ty) ->
        (* adjust: the current term, i.e. the constant, doesn't have
           a binder, so its stack slot should not count *)
        let n = n+1 in
        begin match CCList.get_at_idx n decode.db_stack with
          | None -> errorf_ "De Bruijn index %d not bound" n
          | Some r ->
            match !r with
              | Some v -> T.var v (* use same variable *)
              | None ->
                (* introduce new variable *)
                let v = Var.make ~ty ~name:"self" in
                r := Some v;
                T.var v
        end
      | DataTest _
      | DataSelect _ -> error_ "expected ID, got data test/select"
    end
  | `List [`Atom "LAMBDA"; `List bindings; body] ->
    (* lambda term *)
    let bindings = List.map (parse_var_ ~decode) bindings in
    (* enter scope of variables *)
    within_scope ~decode bindings
      (fun () ->
         let body = parse_term_ ~decode body in
         List.fold_right T.fun_ bindings body)
  | `List [`Atom "ite"; a; b; c] ->
    let a = parse_term_ ~decode a in
    let b = parse_term_ ~decode b in
    let c = parse_term_ ~decode c in
    T.ite a b c
  | `List [`Atom "="; a; b] ->
    let a = parse_term_ ~decode a in
    let b = parse_term_ ~decode b in
    T.eq a b
  | `List [`Atom "not"; f] ->
    let f = parse_term_ ~decode f in
    T.not_ f
  | `List (`Atom "and" :: l) ->
    T.and_ (List.map (parse_term_ ~decode) l)
  | `List (`Atom "or" :: l) ->
    T.or_ (List.map (parse_term_ ~decode) l)
  | `List [`Atom "forall"; `List bindings; f] ->
    let bindings = List.map (parse_var_ ~decode) bindings in
    within_scope ~decode bindings
      (fun () ->
         let f = parse_term_ ~decode f in
         List.fold_right T.forall bindings f)
  | `List [`Atom "exists"; `List bindings; f] ->
    let bindings = List.map (parse_var_ ~decode) bindings in
    within_scope ~decode bindings
      (fun () ->
         let f = parse_term_ ~decode f in
         List.fold_right T.exists bindings f)
  | `List [`Atom "=>"; a; b] ->
    let a = parse_term_ ~decode a in
    let b = parse_term_ ~decode b in
    T.imply a b
  | `List (`Atom _ as f :: l) ->
    begin match parse_atom_ ~decode f, l with
      | ID f, _ ->
        (* regular function app *)
        let l = List.map (parse_term_ ~decode) l in
        T.app f l
      | De_bruijn _, _ -> error_ "invalid arity for De Bruijn index"
      | DataTest c, [t] ->
        let t = parse_term_ ~decode t in
        T.data_test c t
      | DataTest _, _ -> error_ "invalid arity for DataTest"
      | DataSelect (c,n), [t] ->
        let t = parse_term_ ~decode t in
        T.data_select c n t
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
    else match T.view t with
      | FO.Fun (v, t') ->
        let vars, body = get_args t' (n-1) in
        v :: vars, body
      | _ -> errorf_ "expected %d-ary function,@ got `@[%a@]`" n FO.pp_term t
  in
  (* parse term, then convert into [vars -> decision-tree] *)
  let t = parse_term_ ~decode term in
  let vars, body = get_args t n in
  (* change the shape of [body] so it looks more like a decision tree *)
  let dt = FO.Util.dt_of_term ~vars body in
  Utils.debugf ~section 5 "@[<2>turn term `@[%a@]`@ into DT `@[%a@]`@]"
    (fun k->k FO.pp_term body (Model.DT.pp FO.pp_term' FO.pp_ty) dt);
  dt

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
    errorf_ "could not find kind of %a" ID.pp id

(* state: decode_state *)
let parse_model_ ~decode : Sexp_lib.t -> (_,_) Model.t = function
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
                 Model.add_const m (T.const id, t, kind)
               | `Fun n ->
                 let dt = parse_fun_ ~decode ~arity:n term in
                 Model.add_value m (T.const id, dt, kind)
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
                                        let name = const_of_ty_nth ~decode gty i in
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
    (Utils.pp_seq ~sep:" " pp_mquery)
    (ID.Tbl.to_seq decode.symbols)

(* read model from CVC4 instance [s] *)
let get_model_ ~print_model ~decode s : (_,_) Model.t =
  Utils.debugf ~section 3 "@[<2>ask for model with@ %a@]"
    (fun k -> k send_get_model_ decode);
  fpf s.fmt "%a@." send_get_model_ decode;
  (* read result back *)
  match DSexp.next s.sexp with
    | `Error e -> error_ e
    | `End -> error_ "unexpected end of input from CVC4: expected model"
    | `Ok sexp ->
      if print_model
      then Format.eprintf "@[raw model:@ @[<hv>%a@]@]@." Sexp_lib.pp sexp;
      let m = parse_model_ ~decode sexp in
      (* check all symbols are defined *)
      let ok =
        List.length m.Model.values
        + List.length m.Model.finite_types
        =
        ID.Tbl.length decode.symbols
      in
      if not ok then error_ "some symbols are not defined in the model";
      m

(* read the result *)
let read_res_ ~info ~print_model ~decode s =
  try match DSexp.next s.sexp with
    | `Ok (`Atom "unsat") ->
      Utils.debug ~section 5 "CVC4 returned `unsat`";
      Res.Unsat (Lazy.force info)
    | `Ok (`Atom "sat") ->
      Utils.debug ~section 5 "CVC4 returned `sat`";
      let m = if ID.Tbl.length decode.symbols = 0
        then Model.empty
        else get_model_ ~print_model ~decode s
      in
      Res.Sat (m, Lazy.force info)
    | `Ok (`Atom "unknown") ->
      Utils.debug ~section 5 "CVC4 returned `unknown`";
      Res.Unknown [Res.U_other (Lazy.force info, "")]
    | `Ok (`List [`Atom "error"; `Atom s]) ->
      Utils.debugf ~section 5 "@[<2>CVC4 returned `error %s`@]" (fun k->k s);
      Res.Unknown [Res.U_backend_error (Lazy.force info, cvc4_error_ s)]
    | `Ok sexp ->
      let msg = CCFormat.sprintf "@[unexpected answer from CVC4:@ `%a`@]"
          Sexp_lib.pp sexp
      in
      Res.Unknown [Res.U_backend_error (Lazy.force info, msg)]
    | `Error e -> Res.Error (Error e, Lazy.force info)
    | `End ->
      Utils.debug ~section 5 "no answer from CVC4, assume it timeouted";
      Res.Unknown [Res.U_timeout (Lazy.force info)]
  with
    | Backend_err msg ->
      Res.Unknown [Res.U_backend_error (Lazy.force info, msg)]

(* the set of options given to every instance of CVC4 *)
let basic_options =
  "--lang smt --finite-model-find \
   --uf-ss-fair-monotone --no-condense-function-values"

let mk_info ~options (decode:decode_state): Res.info =
  let time = Utils.Time.get_timer decode.timer in
  let message = Printf.sprintf "options: `%s %s`" basic_options options in
  Res.mk_info ~backend:"cvc4" ~time ~message ()

let res t = match t.res with
  | Some r -> r
  | None when t.closed ->
    let r = Res.Unknown [Res.U_timeout (mk_info ~options:t.options t.decode)] in
    t.res <- Some r;
    r
  | None ->
    let info = lazy (mk_info ~options:t.options t.decode) in
    let r =
      try read_res_ ~info ~print_model:t.print_model ~decode:t.decode t
      with e -> Res.Error (e, Lazy.force info)
    in
    t.res <- Some r;
    r

(* once processed, the problem also contains the set of symbols to
   read back from the model, and type witnesses *)
type processed_problem = decode_state * problem

(* is [ty] a finite (uninterpreted) type? *)
let is_finite_ decode ty = match Ty.view ty with
  | FO.TyApp (id, _) -> get_kind ~decode id = Model.Symbol_utype
  | _ -> false

(* does two things:
    - add some dummy constants for uninterpreted types (for asking for
        the type's domain later)
    - compute the set of symbols for which we want the model's value *)
let preprocess pb : processed_problem =
  let kinds = FO.Util.problem_kinds pb in
  let n = ref 0 in
  let state = create_decode_state ~kinds () in
  let decl state id c = ID.Tbl.add state.symbols id c in
  let add_db_prefix state c ty =
    Hashtbl.replace state.db_prefixes c ty
  in
  (* if some types in [l] do not have a witness, add them to [[stmt]] *)
  let add_ty_witnesses stmt l =
    List.fold_left
      (fun acc gty ->
         if not (is_finite_ state gty) || GTy_map.mem gty state.witnesses
         then acc (* already declared a witness for [gty], or [gty] is not
                     a finite type *)
         else (
           (* add a dummy constant *)
           let c = ID.make (CCFormat.sprintf "__nun_card_witness_%d" !n) in
           incr n;
           (* declare [c] *)
           let ty_c = [], gty in
           decl state c (Q_type gty);
           state.witnesses <- GTy_map.add gty c state.witnesses;
           FO.Decl (c, ty_c,[]) :: acc
         ))
      [stmt] l
    |> List.rev
  in
  (* gather list of (possibly parametrized) types occurring in [stmt],
     add witnesses for them *)
  let add_ty_witnesses_gen stmt =
    let tys =
      FO.tys_of_statement stmt
      |> Sequence.flat_map FO.Ty.to_seq
      |> Sequence.sort_uniq ~cmp:FO.Ty.compare
      |> Sequence.to_rev_list
    in
    add_ty_witnesses stmt tys
  in
  let pb =
    FO.Problem.flat_map ~meta:(FO.Problem.meta pb)
      (fun stmt -> match stmt with
         | FO.Decl (id,(args,_),_) ->
           let len = List.length args in
           begin if len=0
             then decl state id Q_const
             else decl state id (Q_fun len)
           end;
           (* if args contains composite types, add witnesses for them *)
           add_ty_witnesses stmt args
         | FO.CardBound (id,_,_)
         | FO.TyDecl (id,0,_) ->
           add_ty_witnesses stmt [gty_const id]
         | FO.MutualTypes (`Codata, l) ->
           List.iter
             (fun tydef ->
                (* use De Bruijn prefixes *)
                let ty = gty_const tydef.FO.ty_name in
                let c = const_of_ty ~decode:state ty in
                Utils.debugf ~section 5 "@[<2>declare `%s` as De Bruijn prefix@]" (fun k->k c);
                add_db_prefix state c ty)
             l.FO.tys_defs;
           add_ty_witnesses_gen stmt
         | FO.TyDecl _ (* witnesses will be added on demand *)
         | FO.Axiom _
         | FO.Goal _
         | FO.MutualTypes (_,_) -> add_ty_witnesses_gen stmt)
      pb
  in
  state, pb

(* the command line to invoke CVC4 *)
let mk_cvc4_cmd_ timeout options =
  let timeout_hard = int_of_float (timeout +. 1.50001) in
  let timeout_ms = int_of_float (timeout *. 1000.) in
  Printf.sprintf
    "ulimit -t %d; exec cvc4 --tlimit=%d --hard-limit %s %s"
    timeout_hard timeout_ms basic_options options

let solve ?(options="") ?deadline ?(print=false) ?(print_model=false) pb =
  let now = Unix.gettimeofday() in
  let deadline = match deadline with Some s -> s | None -> now +. 30. in
  (* preprocess first *)
  let decode, problem' = preprocess pb in
  if print then (
    Format.printf "@[<v2>SMT problem:@ %a@]@." pp_problem (decode, problem');
  );
  (* enough time remaining? *)
  if now +. 0.1 > deadline then (
    let message = Printf.sprintf "options: `%s`" options in
    let info = Res.mk_info ~backend:"cvc4" ~time:0. ~message () in
    S.Fut.return (Res.Unknown [Res.U_timeout info], S.No_shortcut)
  ) else (
    Utils.debug ~section 1 "calling cvc4";
    let timeout = deadline -. now in
    assert (timeout > 0.);
    let cmd = mk_cvc4_cmd_ timeout options in
    S.popen cmd
      ~f:(fun (oc,ic) ->
        let s = create_ ~options ~print_model ~decode (ic,oc) in
        send_ s problem';
        let r = res s in
        Utils.debugf ~lock:true ~section 3 "@[<2>result: %a@]"
          (fun k->k (Res.pp FO.pp_term' FO.pp_ty) r);
        close s;
        match r with
          | Res.Sat (_,_) -> r, S.Shortcut
          | Res.Unsat i ->
            (* beware, this "unsat" might be wrong *)
            if pb.FO.Problem.meta.ProblemMetadata.unsat_means_unknown
            then Res.Unknown [Res.U_incomplete i], S.No_shortcut
            else Res.Unsat i, S.Shortcut
          | Res.Unknown _ -> r, S.No_shortcut
          | Res.Error (e,_) ->
            Utils.debugf ~lock:true ~section 1
              "@[<2>error while running CVC4@ with `%s`:@ @[%s@]@]"
              (fun k->k cmd (Printexc.to_string e));
            r, S.Shortcut
      )
    |> S.Fut.map
      (function
        | E.Ok x -> fst x
        | E.Error e ->
          let info = mk_info ~options decode in
          Res.Error (e,info), S.Shortcut)
  )

let is_available () =
  try
    let res = Sys.command "which cvc4 > /dev/null 2> /dev/null" = 0 in
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
let call
    ?(options="") ?prio ?slice
    ~print ~dump ~print_smt ~print_model
    problem
  =
  if print then (
    Format.printf "@[<v2>FO problem:@ %a@]@." FO.pp_problem problem;
  );
  begin match dump with
    | None ->
      Scheduling.Task.of_fut ?prio ?slice
        (fun ~deadline () ->
           solve ~options ~deadline ~print:print_smt ~print_model problem)
    | Some file ->
      let file = file ^ ".cvc4.smt2" in
      Utils.debugf ~section 1 "output CVC4 problem into `%s`" (fun k->k file);
      let info =
        CCIO.with_out file
          (fun oc ->
             let out = Format.formatter_of_out_channel oc in
             let decode, problem' = preprocess problem in
             Format.fprintf out
               "@[<v>; generated by Nunchaku@ %a@]@."
               pp_problem (decode, problem');
             mk_info ~options decode)
      in
      S.Task.return (Res.Unknown [Res.U_other (info, "--dump")]) S.No_shortcut
  end

let pipes
    ?(options=[""]) ?slice ?(schedule_options=true)
    ~print ~dump ~print_smt ~print_model
    () =
  let slice =
    if schedule_options
    then (
      let n = List.length options in
      assert (n > 0);
      (* each process' slice is only [1/n] of the global CVC4 slice *)
      CCOpt.map (fun s -> s /. float n) slice
    ) else slice
  in
  let encode pb =
    List.mapi
      (fun i options ->
         (* only print for the first task *)
         let print = print && i=0 in
         let print_smt = print_smt && i=0 in
         let prio = 30 + 10 * i in
         call ?slice ~options ~prio ~print ~dump ~print_smt ~print_model pb)
      options, ()
  in
  let input_spec =
    Transform.Features.(of_list
        [ Ty, Mono; Eqn, Absent; Copy, Absent; Match, Absent ])
  in
  Transform.make ~input_spec ~name ~encode ~decode:(fun _ x -> x) ()


