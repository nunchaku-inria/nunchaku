
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Interface to CVC4} *)

module E = CCError
module Var = NunVar
module ID = NunID
module Sol = NunSolver_intf

module FO = NunFO
module T = NunFO.Default.T
module Ty = NunFO.Default.Ty
module F = NunFO.Default.Formula

module DSexp = CCSexpM.MakeDecode(struct
  type 'a t = 'a
  let return x = x
  let (>>=) x f = f x
end)

(** {2 CVC4} *)
module CVC4 = struct
  (* the solver is dealt with through stdin/stdout *)
  type t = {
    oc : out_channel;
    fmt : Format.formatter; (* prints on [oc] *)
    ic : in_channel;
    mutable sexp : DSexp.t;
    mutable closed : bool;
    mutable res : Sol.Res.t option;
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

  let create_ ~timeout () =
    let cmd = Printf.sprintf "cvc4 --tlimit-per=%d" (timeout * 1000) in
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
      closed=false;
      sexp=DSexp.make ~bufsize:4_000 (input ic);
      res=None;
    } in
    Gc.finalise close s; (* close on finalize *)
    s

  let fpf = Format.fprintf

  (* print type (a monomorphic type) in SMT *)
  let rec print_ty out ty = match Ty.view ty with
    | FO.TyBuiltin b ->
        begin match b with
        | FO.TyBuiltin.Prop -> CCFormat.string out "Bool"
        end
    | FO.TyApp (f, []) -> ID.print out f
    | FO.TyApp (f, l) ->
        fpf out "@[(%a@ %a)@]"
          ID.print f
          (CCFormat.list ~start:"" ~stop:"" ~sep:" " print_ty) l

  (* print type in SMT syntax *)
  let print_ty_decl out ty =
    let args, ret = ty in
    fpf out "%a %a"
      (CCFormat.list ~start:"(" ~stop:")" ~sep:" " print_ty) args print_ty ret

  let rec print_term out t = match T.view t with
    | FO.Builtin b ->
        begin match b with
        | FO.Builtin.Int n -> CCFormat.int out n
        end
    | FO.Var v -> Var.print out v
    | FO.App (f,[]) -> ID.print out f
    | FO.App (f,l) ->
        fpf out "(@[%a@ %a@])"
          ID.print f (CCFormat.list ~start:"" ~stop:"" ~sep:" " print_term) l
    | FO.Let (v,t,u) ->
        fpf out "@[<3>(let@ ((%a %a))@ %a@])"
          Var.print v print_term t print_term u

  let rec print_form out t = match F.view t with
    | FO.Atom t -> print_term out t
    | FO.True -> CCFormat.string out "true"
    | FO.False -> CCFormat.string out "false"
    | FO.Eq (a,b) -> fpf out "(@[=@ %a@ %a@])" print_term a print_term b
    | FO.And [] -> print_form out F.true_
    | FO.And [f] -> print_form out f
    | FO.And l ->
        fpf out "(@[and@ %a@])"
          (CCFormat.list ~start:"" ~stop:"" ~sep:" " print_form) l
    | FO.Or [] -> print_form out F.false_
    | FO.Or [f] -> print_form out f
    | FO.Or l ->
        fpf out "(@[or@ %a@])"
          (CCFormat.list ~start:"" ~stop:"" ~sep:" " print_form) l
    | FO.Not f ->
        fpf out "(@[not@ %a@])" print_form f
    | FO.Imply (a,b) ->
        fpf out "(@[=>@ %a@ %a@])" print_form a print_form b
    | FO.Equiv (_,_) -> NunUtils.not_implemented "cvc4.print_equiv" (* TODO *)
    | FO.Forall (v,f) ->
        fpf out "(@[<2>forall@ ((%a %a))@ %a@])"
          Var.print v print_ty (Var.ty v) print_form f
    | FO.Exists (v,f) ->
        fpf out "(@[<2>exists@ ((%a %a))@ %a@])"
          Var.print v print_ty (Var.ty v) print_form f

  let print_statement out = function
    | Sol.Problem.TyDecl (id,arity) ->
        fpf out "(@[declare-sort@ %a@ %d@])" ID.print id arity
    | Sol.Problem.Decl (v,ty) ->
        fpf out "(@[<2>declare-fun@ %a@ %a@])"
          ID.print v print_ty_decl ty
    | Sol.Problem.Def (_,_,_) ->
        NunUtils.not_implemented "cvc4.output definition" (* TODO *)
    | Sol.Problem.Axiom t ->
        fpf out "(@[(assert %a)@])" print_form t
    | Sol.Problem.FormDef (_,_) ->
        NunUtils.not_implemented "cvc4.output formula def" (* TODO *)

  let send_ s problem =
    List.iter
      (fpf s.fmt "%a@." print_statement)
      problem.Sol.Problem.statements;
    output_string s.oc "(check-sat)\n";
    flush s.oc;
    ()

  (* read model from CVC4 *)
  let get_model_ _ = assert false

  (* read the result *)
  let read_res_ s =
    match DSexp.next s.sexp with
    | `Ok (`Atom "unsat") ->
        Sol.Res.Unsat
    | `Ok (`Atom "sat") ->
        let m = get_model_ s in
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
        let r = read_res_ t in
        t.res <- Some r;
        r

  let solve ?(timeout=30) problem =
    let s = create_ ~timeout () in
    send_ s problem;
    s
end

let solver = (module CVC4 : Sol.S)
