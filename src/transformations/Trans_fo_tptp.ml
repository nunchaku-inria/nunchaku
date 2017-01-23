
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Translation FO/FO_tptp} *)

open Nunchaku_core

module To_tptp = struct
  open FO
  module TT = FO_tptp

  exception Error of string
  let () = Printexc.register_printer
      (function
        | (Error e) -> Some (Utils.err_sprintf "conversion to TPTP: %s" e)
        | _ -> None)

  let error_ msg = raise (Error msg)
  let errorf_ msg = Utils.exn_ksprintf ~f:error_ msg

  let is_unitype_ ty = match Ty.view ty with
    | TyBuiltin `Unitype ->  true
    | _ -> false

  (* check the type of [v] *)
  let conv_var v =
    if is_unitype_ (Var.ty v)
    then Var.set_ty v ~ty:TT.Unitype
    else errorf_ "variable `%a` does not have type `unitype`" Var.print_full v

  (* intermediate structure, for having only one conversion into terms and
     into formulas *)
  type term_or_form =
    | T of TT.term
    | F of TT.form

  (* convert term *)
  let rec conv_rec subst t : term_or_form = match T.view t with
    | Builtin _ -> assert false (* TODO *)
    | Var v ->
      begin match Var.Subst.find ~subst v with
        | Some t -> T t
        | None -> T (TT.var (conv_var v))
      end
    | App (f,l) -> T (TT.app f (List.map (conv_as_term subst) l))
    | Undefined t -> conv_rec subst t
    | Mu (_,_)
    | DataTest (_,_)
    | DataSelect (_,_,_)
    | Undefined_atom _
    | Unparsable _ ->
      errorf_ "cannot convert `@[%a@]` to TPTP" print_term t
    | Fun (_,_) -> errorf_ "cannot convert function `@[%a@]` to TPTP" print_term t
    | Let (v,t,u) ->
      (* expand `let` *)
      let t = conv_as_term subst t in
      let subst = Var.Subst.add ~subst v t in
      conv_rec subst u
    | Ite (_,_,_) -> error_ "fo_to_tptp: unexpected `ite`"
    | True -> T TT.true_
    | False -> T TT.false_
    | Eq (a,b) -> F (TT.eq (conv_as_term subst a) (conv_as_term subst b))
    | And l -> F (TT.and_ (List.map (conv_as_form subst) l))
    | Or l -> F (TT.or_ (List.map (conv_as_form subst) l))
    | Not f -> F (TT.not_ (conv_as_form subst f))
    | Imply (a,b) -> F (TT.imply (conv_as_form subst a) (conv_as_form subst b))
    | Equiv (a,b) -> F (TT.equiv (conv_as_form subst a) (conv_as_form subst b))
    | Forall (v,f) ->
      let v' = conv_var v in
      let subst = Var.Subst.add v (TT.var v') ~subst in
      F (TT.forall v' (conv_as_form subst f))
    | Exists (v,f) ->
      let v' = conv_var v in
      let subst = Var.Subst.add v (TT.var v') ~subst in
      F (TT.exists v' (conv_as_form subst f))

  and conv_as_term subst t = match conv_rec subst t with
    | T t -> t
    | F _ -> errorf_ "@[expected term,@ but `@[%a@]` is a formula@]" print_term t

  and conv_as_form subst t = match conv_rec subst t with
    | F t -> t
    | T t -> TT.atom t

  let conv_form = conv_as_form Var.Subst.empty

  let conv_statement st = match st with
    | TyDecl _
    | Decl _ -> None
    | MutualTypes _ -> errorf_ "@[cannot convert@ statement `@[%a@]`@]" print_statement st
    | CardBound _ -> assert false (* TODO warning? *)
    | Axiom f -> Some (TT.axiom (conv_form f))
    | Goal f -> Some (TT.axiom (conv_form f)) (* careful, not a conjecture *)

  let conv_problem pb =
    let res = CCVector.filter_map conv_statement (Problem.statements pb) in
    { FO_tptp.
      pb_statements=res;
      pb_meta=Problem.meta pb;
    }
end

module Of_tptp = struct
  open FO
  module TT = FO_tptp

  let conv_ty = function
    | TT.Unitype -> Ty.builtin `Unitype

  let conv_var = Var.update_ty ~f:conv_ty

  let gen_undefined_ =
    let r = ref 0 in
    fun () ->
      let id = ID.make_f "undefined_%d" !r in
      incr r;
      id

  let rec conv_term = function
    | TT.App (id, args) -> T.app id (List.map conv_term args)
    | TT.Var v -> T.var (conv_var v)
    | TT.True -> T.true_
    | TT.False -> T.false_
    | TT.Undefined_atom l ->
      (* a new undefined atom of type "unitype" *)
      let l = List.map conv_term l in
      T.undefined_atom (gen_undefined_ ()) ([], Ty.builtin `Unitype) l

  let conv_form _ = assert false (* TODO *)
end

let pipe =
  let decode () res =
    Problem.Res.map res ~term:Of_tptp.conv_term ~ty:Of_tptp.conv_ty
  in
  Transform.make
    ~name:"conv_tptp"
    ~encode:(fun pb -> To_tptp.conv_problem pb, ()) ~decode
    ()
