
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Higher-Order Terms}

  To be used after type inference, i.e. converted from {!NunTerm_typed}
*)

(*$inject
  let pterm = NunLexer.HO.term_of_str_exn

  module U = Util(Default)
  module Su = SubstUtil(Default)
  module TyI = NunType_intf
*)

module ID = NunID
module Var = NunVar
module Sig = NunSignature
module TI = NunTermInner

type id = NunID.t
type 'a var = 'a NunVar.t
type 'a or_error = [`Ok of 'a | `Error of string]
type 'a printer = Format.formatter -> 'a -> unit

module Builtin = TI.Builtin
module TyBuiltin = TI.TyBuiltin

type 'a view =
  | Const of id (** top-level symbol *)
  | Var of 'a var (** bound variable *)
  | App of 'a * 'a list
  | AppBuiltin of Builtin.t * 'a list (** built-in operation *)
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
    | TI.AppBuiltin (b,l) -> AppBuiltin(b,l)
    | TI.Bind (b,v,t) -> Bind(b,v, t)
    | TI.Let (v,t,u) -> Let(v,t,u)
    | TI.Match (t,l) -> Match (t, l)
    | TI.TyBuiltin b -> TyBuiltin b
    | TI.TyArrow (a,b) -> TyArrow (a, b)
    | TI.TyMeta _ -> assert false
end

(** {2 Default Representation}

  As a private alias to the default {!NunTermInner} representation, basically
  removing the meta case *)

module Default = Make(TI.Default)

(*$T
  TyI.returns_Type ~repr:U.as_ty (U.ty_type())
  TyI.returns_Type ~repr:U.as_ty U.(ty_arrow (ty_prop()) (ty_type()))
  not (TyI.returns_Type ~repr:U.as_ty U.(ty_arrow (ty_type()) (ty_prop())))
*)

let default = (module Default : S with type T.t = TI.Default.t)

(** {2 Type Erasure} *)

module Untyped = NunUntypedAST

module Erase(T : S)
: sig
  type ctx

  val create: unit -> ctx

  val erase: ctx:ctx -> T.t -> Untyped.term
end = struct
  type ctx = {
    map: (string * int) ID.Tbl.t; (* remember results *)
    disamb: (string, int list) Hashtbl.t;  (* name -> set of nums *)
  }
  (* map ID to names, without collisions *)

  let create () = {
    map=ID.Tbl.create 32;
    disamb=Hashtbl.create 32;
  }

  (* find smallest int not in list *)
  let rec find_smallest_ n l =
    if List.mem n l then find_smallest_ (n+1) l else n

  (* find an identifier *)
  let find_ ~ctx id =
    try fst (ID.Tbl.find ctx.map id)
    with Not_found ->
      let name = ID.name id in
      let l = try Hashtbl.find ctx.disamb name with Not_found -> [] in
      let n = find_smallest_ 0 l in
      let name' = if n=0 then name else Printf.sprintf "%s/%d" name n in
      Hashtbl.replace ctx.disamb name (n::l);
      ID.Tbl.replace ctx.map id (name', n);
      name'

  (* remove an identifier *)
  let remove_ ~ctx id =
    let _, n = ID.Tbl.find ctx.map id in
    ID.Tbl.remove ctx.map id;
    let name = ID.name id in
    let l = Hashtbl.find ctx.disamb name in
    let l = CCList.Set.remove n l in
    if l=[]
    then Hashtbl.remove ctx.disamb name
    else Hashtbl.replace ctx.disamb name l

  (* enter the scope of [v] *)
  let enter_ ~ctx v f =
    let name = find_ ~ctx (Var.id v) in
    try
      let x = f name in
      remove_ ~ctx (Var.id v);
      x
    with e ->
      remove_ ~ctx (Var.id v);
      raise e

  let erase ~ctx t =
    let rec aux t = match T.repr t with
    | AppBuiltin (`Ite, [a;b;c]) ->
        Untyped.ite (aux a)(aux b)(aux c)
    | AppBuiltin (b,l) ->
        let b = match b with
          | `True  -> `True
          | `False -> `False
          | `Not -> `Not
          | `Or -> `Or
          | `And -> `And
          | `Imply -> `Imply
          | `Equiv -> `Equiv
          | `Eq  -> `Eq
          | `DataSelect _
          | `DataTest _
          | `Ite -> assert false (* wrong arity: those are not terms *)
        in
        Untyped.app (Untyped.builtin b) (List.map aux l)
    | Const id -> Untyped.var (find_ ~ctx id)
    | Var v -> Untyped.var (find_ ~ctx (Var.id v))
    | App (f,l) -> Untyped.app (aux f) (List.map aux l)
    | Bind (b,v,t) ->
        enter_typed_var_ ~ctx v
          (fun v' ->
            let t = aux t in
            match b with
            | `Fun -> Untyped.fun_ v' t
            | `Forall -> Untyped.forall v' t
            | `Exists -> Untyped.exists v' t
            | `TyForall -> Untyped.ty_forall (fst v') t
          )
    | Let (v,t,u) ->
        let t = aux t in
        enter_ ~ctx v
          (fun v' ->
            Untyped.let_ v' t (aux u)
          )
    | Match _ -> assert false (* TODO *)
    | TyBuiltin b ->
        let b = match b with
          | `Prop -> `Prop
          | `Type -> `Type
          | `Kind -> failwith "HO.erase: cannot erase Kind"
        in
        Untyped.builtin b
    | TyArrow (a,b) -> Untyped.ty_arrow (aux a) (aux b)
    (* enter a typed variable *)
    and enter_typed_var_ ~ctx v f =
      enter_ ~ctx v
        (fun v' ->
          let ty = aux (Var.ty v) in
          f (v', Some ty)
        )
    in
    aux t
end

(** {2 Conversion of UntypedAST to HO, without Type-Checking} *)

module OfUntyped(T : TI.S)
: sig
  module TPoly : S with type T.t = T.t

  exception Error of Untyped.term * string

  val convert_term : Untyped.term -> T.t
  (** Convert an untyped parse tree term into a polymorphic term
      @raise Error if some variable types could not be trivially inferred *)
end = struct
  module A = NunUntypedAST
  module Loc = NunLocation
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
          U.app (aux f) (List.map aux l)
      | A.Wildcard -> error_ t "wildcard not supported"
      | A.Builtin b ->
          begin match b with
          | `Prop -> U.ty_prop
          | `Type -> U.ty_type
          | `Not -> U.ty_builtin `Prop
          | `And -> U.builtin `And
          | `Or -> U.builtin `Or
          | `True -> U.builtin `True
          | `False -> U.builtin `False
          | `Imply -> U.builtin `Imply
          | `Eq | `Equiv ->
              error_ t "unapplied equality"
          end
      | A.AtVar s
      | A.Var s ->
          begin try
            match Hashtbl.find env s with
            | ID id -> U.const id
            | Var v -> U.var v
          with Not_found ->
            (* constant, not variable *)
            let id = ID.make ~name:s in
            Hashtbl.add env s (ID id);
            U.const id
          end
      | A.MetaVar _ -> error_ t "meta variable"
      | A.Exists ((_, None), _)
      | A.Forall ((_, None), _)
      | A.Fun ((_, None), _) -> error_ t "untyped variable"
      | A.Fun ((v, Some ty),t) ->
          enter_var_ ~ty v (fun v -> U.fun_ v (aux t))
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
