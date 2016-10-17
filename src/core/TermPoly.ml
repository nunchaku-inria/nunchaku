
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Higher-Order Terms}

  To be used after type inference, i.e. converted from {!Term_typed}
*)

(*$inject
  let pterm = Lexer.HO.term_of_str_exn

  module U = Util(Default)
  module Su = SubstUtil(Default)
  module TyI = Type_intf
*)

module ID = ID
module Var = Var
module Sig = Signature
module TI = TermInner

type id = ID.t
type 'a var = 'a Var.t
type 'a or_error = ('a, string) CCResult.t
type 'a printer = Format.formatter -> 'a -> unit

module Builtin = TI.Builtin
module TyBuiltin = TI.TyBuiltin

type 'a view =
  | Const of id (** top-level symbol *)
  | Var of 'a var (** bound variable *)
  | App of 'a * 'a list
  | Builtin of 'a Builtin.t (** built-in operation *)
  | Bind of TI.Binder.t * 'a var * 'a
  | Let of 'a var * 'a * 'a
  | Match of 'a * 'a TI.cases (** shallow pattern-match *)
  | TyBuiltin of TyBuiltin.t (** Builtin type *)
  | TyArrow of 'a * 'a  (** Arrow type *)

module type S = sig
  module T : TI.REPR
  type t = T.t

  val repr : T.t -> T.t view
  (** View that fails on meta variables *)
end

module Make(T : TI.REPR)
: S with module T = T
= struct
  module T = T
  type t = T.t

  let repr t = match T.repr t with
    | TI.Const id -> Const id
    | TI.Var v -> Var v
    | TI.App (f,l) -> App (f, l)
    | TI.Builtin b -> Builtin b
    | TI.Bind (b,v,t) -> Bind(b,v, t)
    | TI.Let (v,t,u) -> Let(v,t,u)
    | TI.Match (t,l) -> Match (t, l)
    | TI.TyBuiltin b -> TyBuiltin b
    | TI.TyArrow (a,b) -> TyArrow (a, b)
    | TI.TyMeta _ -> assert false
end

(** {2 Default Representation}

  As a private alias to the default {!TermInner} representation, basically
  removing the meta case *)

module Default = Make(TI.Default)

(*$T
  TyI.returns_Type ~repr:U.as_ty (U.ty_type())
  TyI.returns_Type ~repr:U.as_ty U.(ty_arrow (ty_prop()) (ty_type()))
  not (TyI.returns_Type ~repr:U.as_ty U.(ty_arrow (ty_type()) (ty_prop())))
*)

let default = (module Default : S with type T.t = TI.Default.t)

module Untyped = UntypedAST

(** {2 Conversion of UntypedAST to HO, without Type-Checking} *)

module OfUntyped(T : TI.S)
: sig
  module TPoly : S with type T.t = T.t

  exception Error of Untyped.term * string

  val convert_term : Untyped.term -> T.t
  (** Convert an untyped parse tree term into a polymorphic term
      @raise Error if some variable types could not be trivially inferred *)
end = struct
  module A = UntypedAST
  module Loc = Location
  module TPoly = Make(T)
  module U = TI.Util(T)

  exception Error of A.term * string

  let () = Printexc.register_printer
    (function
      | Error (t,s) ->
          Some (CCFormat.sprintf "of_untyped: error on %a: %s" A.print_term t s)
      | _ -> None
    )

  let error_ t s = raise (Error (t,s))

  type env_cell =
    | ID of ID.t
    | Var of T.t Var.t

  let convert_term t =
    let env = Hashtbl.create 32 in
    let rec aux t = match Loc.get t with
      | A.App (f, l) ->
          begin match Loc.get f, l with
            | A.Builtin `Not, [t] -> U.not_ (aux t)
            | A.Builtin `And, _ -> U.and_ (List.map aux l)
            | A.Builtin `Or, _-> U.or_ (List.map aux l)
            | A.Builtin `Imply, [a;b] -> U.imply (aux a) (aux b)
            | A.Builtin (`Not | `Imply), _ -> error_ t "partially applied builtin"
            | _ -> U.app (aux f) (List.map aux l)
          end
      | A.Var `Wildcard -> error_ t "wildcard not supported"
      | A.Builtin b ->
          begin match b with
          | `Prop -> U.ty_prop
          | `Type -> U.ty_type
          | `True -> U.builtin `True
          | `False -> U.builtin `False
          | `Unitype -> U.ty_unitype
          | `Undefined _ -> error_ t "cannot convert `undefined`"
          | `Eq | `Equiv | `Not | `And | `Or | `Imply ->
              error_ t "partially applied builtin"
          end
      | A.AtVar s
      | A.Var (`Var s) ->
          begin try
            match Hashtbl.find env s with
            | ID id -> U.const id
            | Var v -> U.var v
          with Not_found ->
            (* constant, not variable *)
            let id = ID.make s in
            Hashtbl.add env s (ID id);
            U.const id
          end
      | A.MetaVar _ -> error_ t "meta variable"
      | A.Exists ((_, None), _)
      | A.Forall ((_, None), _)
      | A.Mu ((_,None), _)
      | A.Fun ((_, None), _) -> error_ t "untyped variable"
      | A.Fun ((v, Some ty),t) ->
          enter_var_ ~ty v (fun v -> U.fun_ v (aux t))
      | A.Mu ((v, Some ty),t) ->
          enter_var_ ~ty v (fun v -> U.mu v (aux t))
      | A.Let _ ->
          error_ t "`let` unsupported (no way of inferring the type)"
      | A.Match _ ->
          error_ t "`match` unsupported (no way of inferring the type of variables)"
      | A.Ite (a,b,c) -> U.ite (aux a) (aux b) (aux c)
      | A.Forall ((v,Some ty),t) ->
          enter_var_ ~ty v (fun v -> U.forall v (aux t))
      | A.Exists ((v, Some ty),t) ->
          enter_var_ ~ty v (fun v -> U.exists v (aux t))
      | A.TyArrow (a,b) -> U.ty_arrow (aux a) (aux b)
      | A.TyForall (v,t) ->
          enter_var_ ~ty:(A.builtin `Type) v
            (fun v -> U.ty_forall v (aux t))
      | A.Asserting (t, l) ->
          let t = aux t in
          let l = List.map aux l in
          U.asserting t l

    (* enter scope of [s] *)
    and enter_var_ s ~ty f =
      let ty = aux ty in
      let v = Var.make ~name:s ~ty in
      Hashtbl.add env s (Var v);
      let x = f v in
      Hashtbl.remove env s;
      x
    in
    aux t
end
