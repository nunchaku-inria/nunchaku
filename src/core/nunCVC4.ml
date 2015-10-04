
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Interface to CVC4} *)

module E = CCError
module Var = NunVar
module Sol = NunSolver_intf

module T = NunTerm_typed
module Ty = T.Ty
module TI = NunTerm_intf
module TyI = NunType_intf

module DSexp = CCSexpM.MakeDecode(struct
  type 'a t = 'a
  let return x = x
  let (>>=) x f = f x
end)

(* TODO: use a special view for terms and types? simplify matchings a lot *)

let wrong_fragment msg = failwith ("CVC4: wrong fragment " ^ msg)

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

  (* print type (a monomorphic type) in SMT *)
  let rec print_ty out ty = match Ty.view ty with
    | TyI.Kind -> wrong_fragment "kind"
    | TyI.Type -> wrong_fragment "type"
    | TyI.Builtin b ->
        begin match b with
        | TyI.Builtin.Prop -> CCFormat.string out "Bool"
        end
    | TyI.Meta (v,_)
    | TyI.Var v -> Var.print out v
    | TyI.App (_, []) -> assert false
    | TyI.App (f,l) ->
        Format.fprintf out "@[(%a@ %a)@]"
          print_ty f
          (CCFormat.list ~start:"" ~stop:"" ~sep:" " print_ty) l
    | TyI.Arrow (_,_)
    | TyI.Forall (_,_) -> wrong_fragment "sub arrow or forall type"

  (* print type in SMT syntax *)
  let print_ty_decl out ty =
    let rec collect ty = match Ty.view ty with
      | TyI.Kind -> wrong_fragment "kind"
      | TyI.Type -> wrong_fragment "type"
      | TyI.Builtin _
      | TyI.Var _
      | TyI.Meta (_,_)
      | TyI.App (_,_) -> [], ty
      | TyI.Arrow (a,b) ->
          let l, ret = collect b in
          a :: l, ret
      | TyI.Forall (_,_) -> wrong_fragment "polymorphic type"
    in
    let args, ret = collect ty in
    Format.fprintf out "%a %a"
      (CCFormat.list ~start:"(" ~stop:")" ~sep:" " print_ty) args print_ty ret

  let rec print_form out t = match T.view t with
    | TI.Builtin b ->
        let s = match b with
          | TI.Builtin.True -> "true"
          | TI.Builtin.False -> "false"
          | TI.Builtin.Not -> "not"
          | TI.Builtin.Or -> "or"
          | TI.Builtin.And -> "and"
          | TI.Builtin.Imply -> "=>"
          | TI.Builtin.Equiv -> "<=>"
        in
        CCFormat.string out s
    | TI.TyMeta (v,_)
    | TI.Var v -> Var.print out v
    | TI.App (_, []) -> assert false
    | TI.App (f,l) ->
        Format.fprintf out "(@[<2>%a@ %a@])"
          print_form f (CCFormat.list ~start:"" ~stop:"" ~sep:" " print_form) l
    | TI.Forall (v,ty,t) ->
        Format.fprintf out "(@[forall ((%a %a)) %a@])"
          Var.print v print_ty ty print_form t
    | TI.Exists (v,ty,t) ->
        Format.fprintf out "(@[exists ((%a %a)) %a@])"
          Var.print v print_ty ty print_form t
    | TI.Let (_,_,_) -> assert false (* TODO *)
    | TI.Fun (_,_,_) -> wrong_fragment "function in formula"
    | TI.TyKind
    | TI.TyType
    | TI.TyBuiltin _
    | TI.TyArrow (_,_)
    | TI.TyForall (_,_) -> wrong_fragment "type in formula"

  let send_ s problem =
    List.iter
      (fun st -> match st with
          | Sol.Problem.Decl (v,ty) ->
              Format.fprintf s.fmt "(@[<2>declare-fun@ %a@ %a@])@."
                Var.print v print_ty_decl ty
          | Sol.Problem.Def (_,_,_) -> assert false (* TODO *)
          | Sol.Problem.Axiom t ->
              Format.fprintf s.fmt "(@[(assert %a)@])@." print_form t
      )
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
