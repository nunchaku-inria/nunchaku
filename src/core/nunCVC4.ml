
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Interface to CVC4} *)

module E = CCError
module Var = NunVar
module ID = NunID
module Sol = NunSolver_intf
module FOI = NunFO

module DSexp = CCSexpM.MakeDecode(struct
  type 'a t = 'a
  let return x = x
  let (>>=) x f = f x
end)

module Make(FO : NunFO.VIEW) = struct
  module FO = FO
  module T = FO.T
  module Ty = FO.Ty
  module F = FO.Formula

  (* for the model *)
  module FOBack = NunFO.Default

  type problem = (FO.Formula.t, FO.T.t, FO.Ty.t) NunFO.Problem.t

  (* the solver is dealt with through stdin/stdout *)
  type t = {
    oc : out_channel;
    fmt : Format.formatter; (* prints on [oc] *)
    ic : in_channel;
    symbols : ID.Set.t; (* set of symbols to ask values for in the model *)
    tbl : (string, ID.t) Hashtbl.t; (* map (stringof ID) -> ID *)
    mutable sexp : DSexp.t;
    mutable closed : bool;
    mutable res : FOBack.T.t Sol.Res.t option;
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
    let cmd = Printf.sprintf "cvc4 --tlimit-per=%d --lang smt"
      (int_of_float (timeout *. 1000.)) in
    let ic, oc = Unix.open_process cmd in
    (* send prelude *)
    output_string oc "(set-option :produce-models true)\n";
    output_string oc "(set-option :interactive-mode true)\n";
    output_string oc "(set-logic QF_UF)\n";
    flush oc;
    (* the [t] instance *)
    let s = {
      oc;
      fmt=Format.formatter_of_out_channel oc;
      ic;
      symbols;
      tbl=Hashtbl.create 32;
      closed=false;
      sexp=DSexp.make ~bufsize:4_000 (input ic);
      res=None;
    } in
    Gc.finalise close s; (* close on finalize *)
    s

  let fpf = Format.fprintf

  (* print problems. [on_id (to_string id) id] is called every time
      and id is printed.  *)
  let print_problem_ ~on_id =
    (* print ID and remember its name for parsing model afterward *)
    let rec print_id out id =
      let name = ID.to_string id in
      on_id name id;
      CCFormat.string out name

    (* print type (a monomorphic type) in SMT *)
    and print_ty out ty = match Ty.view ty with
      | FOI.TyBuiltin b ->
          begin match b with
          | FOI.TyBuiltin.Prop -> CCFormat.string out "Bool"
          end
      | FOI.TyApp (f, []) -> print_id out f
      | FOI.TyApp (f, l) ->
          fpf out "@[(%a@ %a)@]"
            print_id f
            (CCFormat.list ~start:"" ~stop:"" ~sep:" " print_ty) l

    (* print type in SMT syntax *)
    and print_ty_decl out ty =
      let args, ret = ty in
      fpf out "%a %a"
        (CCFormat.list ~start:"(" ~stop:")" ~sep:" " print_ty) args print_ty ret

    and print_term out t = match T.view t with
      | FOI.Builtin b ->
          begin match b with
          | FOI.Builtin.Int n -> CCFormat.int out n
          end
      | FOI.Var v -> Var.print out v
      | FOI.App (f,[]) -> print_id out f
      | FOI.App (f,l) ->
          fpf out "(@[%a@ %a@])"
            print_id f (CCFormat.list ~start:"" ~stop:"" ~sep:" " print_term) l
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
          fpf out "(@[and@ %a@])"
            (CCFormat.list ~start:"" ~stop:"" ~sep:" " print_form) l
      | FOI.Or [] -> CCFormat.string out "false"
      | FOI.Or [f] -> print_form out f
      | FOI.Or l ->
          fpf out "(@[or@ %a@])"
            (CCFormat.list ~start:"" ~stop:"" ~sep:" " print_form) l
      | FOI.Not f ->
          fpf out "(@[not@ %a@])" print_form f
      | FOI.Imply (a,b) ->
          fpf out "(@[=>@ %a@ %a@])" print_form a print_form b
      | FOI.Equiv (_,_) -> NunUtils.not_implemented "cvc4.print_equiv" (* TODO *)
      | FOI.Forall (v,f) ->
          fpf out "(@[<2>forall@ ((%a %a))@ %a@])"
            Var.print v print_ty (Var.ty v) print_form f
      | FOI.Exists (v,f) ->
          fpf out "(@[<2>exists@ ((%a %a))@ %a@])"
            Var.print v print_ty (Var.ty v) print_form f
      | FOI.F_ite (a,b,c) ->
          fpf out "@[<2>(ite@ %a@ %a@ %a)@]"
            print_form a print_form b print_form c

    and print_statement out = function
      | FOI.TyDecl (id,arity) ->
          fpf out "(@[declare-sort@ %a@ %d@])" print_id id arity
      | FOI.Decl (v,ty) ->
          fpf out "(@[<2>declare-fun@ %a@ %a@])"
            print_id v print_ty_decl ty
      | FOI.Def (_,_,_) ->
          NunUtils.not_implemented "cvc4.output definition" (* TODO *)
      | FOI.Axiom t ->
          fpf out "(@[assert@ %a@])" print_form t
      | FOI.Goal t ->
          fpf out "(@[assert@ %a@])" print_form t
      | FOI.FormDef (_,_) ->
          NunUtils.not_implemented "cvc4.output formula def" (* TODO *)

    in
    fun out pb ->
      fpf out "@[<v>%a@]"
        (CCFormat.list ~start:"" ~stop:"" ~sep:"" print_statement )
        pb.FOI.Problem.statements

  let send_ s problem =
    let on_id name id =
      Hashtbl.replace s.tbl name id
    in
    fpf s.fmt "%a@." (print_problem_ ~on_id) problem;
    fpf s.fmt "(check-sat)@.";
    flush s.oc;
    ()

  let print_problem = print_problem_ ~on_id:(fun _ _ -> ())

  (* local error *)
  exception Error of string

  let error_ e = raise (Error e)

  (* parse an identifier *)
  let parse_id_ ~tbl = function
    | `Atom s ->
        begin try Hashtbl.find tbl s
        with Not_found ->
          (* introduced by CVC4 in the model; make a new ID *)
          let id = ID.make ~name:s in
          Hashtbl.replace tbl s id;
          id
        end
    | _ -> error_ "expected ID, got a list"

  (* parse an atomic type *)
  let rec parse_ty_ ~tbl = function
    | `Atom _ as f ->
        let id = parse_id_ ~tbl f in
        FOBack.Ty.const id
    | `List (`Atom _ as f :: l) ->
        let id = parse_id_ ~tbl f in
        let l = List.map (parse_ty_ ~tbl) l in
        FOBack.Ty.app id l
    | _ -> error_ "invalid type"

  let parse_var_ ~tbl = function
    | `List [`Atom _ as v; ty] ->
        let id = parse_id_ ~tbl v in
        let ty = parse_ty_ ~tbl ty in
        Var.of_id ~ty id
    | _ -> error_ "expected typed variable"

  (* parse a ground term *)
  let rec parse_term_ ~tbl = function
    | `Atom _ as t -> FOBack.T.const (parse_id_ ~tbl t)
    | `List [`Atom "LAMBDA"; `List bindings; body] ->
        (* lambda term *)
        let bindings = List.map (parse_var_ ~tbl) bindings in
        let body = parse_term_ ~tbl body in
        List.fold_right FOBack.T.fun_ bindings body
    | `List [`Atom "ite"; a; b; c] ->
        let a = parse_formula_ ~tbl a in
        let b = parse_term_ ~tbl b in
        let c = parse_term_ ~tbl c in
        FOBack.T.ite a b c
    | `List (`Atom _ as f :: l) ->
        let f = parse_id_ ~tbl f in
        let l = List.map (parse_term_ ~tbl) l in
        FOBack.T.app f l
    | `List (`List _ :: _) -> error_ "non first-order list"
    | `List [] -> error_ "expected term, got empty list"

  (* TODO: equiv, imply *)
  and parse_formula_ ~tbl s =
    match s with
    | `Atom "true" -> FOBack.Formula.true_
    | `Atom "false" -> FOBack.Formula.false_
    | `List [`Atom "="; a; b] ->
        let a = parse_term_ ~tbl a in
        let b = parse_term_ ~tbl b in
        FOBack.Formula.eq a b
    | `List [`Atom "not"; f] ->
        let f = parse_formula_ ~tbl f in
        FOBack.Formula.not_ f
    | `List (`Atom "and" :: l) ->
        FOBack.Formula.and_ (List.map (parse_formula_ ~tbl) l)
    | `List (`Atom "or" :: l) ->
        FOBack.Formula.or_ (List.map (parse_formula_ ~tbl) l)
    | `List [`Atom "forall"; `List bindings; f] ->
        let bindings = List.map (parse_var_ ~tbl) bindings in
        let f = parse_formula_ ~tbl f in
        List.fold_right FOBack.Formula.forall bindings f
    | `List [`Atom "exists"; `List bindings; f] ->
        let bindings = List.map (parse_var_ ~tbl) bindings in
        let f = parse_formula_ ~tbl f in
        List.fold_right FOBack.Formula.exists bindings f
    | `List [`Atom "ite"; a; b; c] ->
        let a = parse_formula_ ~tbl a in
        let b = parse_formula_ ~tbl b in
        let c = parse_formula_ ~tbl c in
        FOBack.Formula.f_ite a b c
    | _ ->
        let t = parse_term_ ~tbl s in
        FOBack.Formula.atom t

  (* tbl: string -> ID *)
  let parse_model_ ~tbl = function
    | `Atom _ -> error_ "expected model, got atom"
    | `List assoc ->
      (* parse model *)
      let m = List.fold_left
        (fun m -> function
          | `List [`Atom _ as s; term] ->
              let id = parse_id_ ~tbl s in
              let term = parse_term_ ~tbl term in
              ID.Map.add id term m
          | _ -> error_ "expected pair key/value in the model"
        )
        ID.Map.empty assoc
      in
      m

  (* read model from CVC4 instance [s]
     symbols: set of symbols to get values for
     tbl: string -> ID *)
  let get_model_ ~symbols ~tbl s =
    fpf s.fmt "(@[<hv2>get-value@ %a@])@."
      (ID.Set.print ~start:"(" ~sep:" " ~stop:")" ID.print)
      symbols;
    match DSexp.next s.sexp with
    | `Error e -> error_ e
    | `End -> error_ "unexpected end of input from CVC4: expected model"
    | `Ok sexp ->
        if !Sol.print_model_
          then Format.eprintf "@[raw model:@ @[<hov>%a@]@]@." CCSexpM.print sexp;
        let m = parse_model_ ~tbl sexp in
        (* check all symbols are defined *)
        let ok = ID.Set.to_seq symbols
          |> Sequence.for_all (fun s -> ID.Map.mem s m)
        in
        if not ok then error_ "some symbols are not defined in the model";
        m

  (* read the result *)
  let read_res_ ~symbols ~tbl s =
    match DSexp.next s.sexp with
    | `Ok (`Atom "unsat") ->
        Sol.Res.Unsat
    | `Ok (`Atom "sat") ->
        let m = get_model_ ~symbols ~tbl s in
        Sol.Res.Sat m
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
          try read_res_ ~symbols:t.symbols ~tbl:t.tbl t
          with Error e -> Sol.Res.Error e
        in
        t.res <- Some r;
        r

  (* set of symbols to find a value for in the model *)
  let compute_symbols_ pb =
    FOI.Problem.statements pb
    |> List.fold_left
      (fun acc s -> match s with
        | FOI.Decl (id,_)
        | FOI.Def (id,_,_)
        | FOI.FormDef (id,_) -> ID.Set.add id acc
        | FOI.TyDecl (_,_)
        | FOI.Axiom _
        | FOI.Goal _ -> acc
      ) ID.Set.empty

  let solve ?(timeout=30.) problem =
    let symbols = compute_symbols_ problem in
    let s = create_ ~timeout ~symbols () in
    send_ s problem;
    s
end
