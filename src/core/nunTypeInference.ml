
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Scoping and Type Inference} *)

module A = NunUntypedAST
module E = CCError
module Sym = NunSymbol
module Var = NunVar
module Loc = NunLocation

type 'a or_error = [`Ok of 'a | `Error of string]
type var = Var.t
type loc = Loc.t
type sym = NunSymbol.t

let spf = CCFormat.sprintf

exception ScopingError of string * string * loc option

let () = Printexc.register_printer
  (function
    | ScopingError (v, msg, loc) ->
        Some (spf "scoping error for var %s: %s at %a"
          v msg Loc.print_opt loc)
    | _ -> None
  )

(** {2 Interface For Types} *)
module type TYPE = sig
  include NunType_intf.UNIFIABLE

  val loc : t -> loc option

  val sym : ?loc:loc -> sym -> t
  val var : ?loc:loc -> var -> t
  val app : ?loc:loc -> t -> t list -> t
  val arrow : ?loc:loc -> t -> t -> t
  val forall : ?loc:loc -> var -> t -> t
end

module MStr = Map.Make(String)

(** {2 Conversion from the parse tree} *)

module ConvertType(Ty : TYPE) = struct
  type t = Ty.t

  type env = t MStr.t

  let add_env ~env v ty = MStr.add v ty env

  let prop = Ty.sym Sym.prop

  let rec convert_exn ~env ty =
    let loc = Loc.get_loc ty in
    match Loc.get ty with
      | A.TySym s -> Ty.sym ?loc s
      | A.TyApp (f, l) -> Ty.app ?loc (convert_exn ~env f) (List.map (convert_exn ~env) l)
      | A.TyWildcard -> Ty.var ?loc (Var.make ~name:"_")
      | A.TyVar v ->
          begin try MStr.find v env
          with Not_found ->
            raise (ScopingError (v, "not bound in environment", loc))
          end
      | A.TyArrow (a,b) -> Ty.arrow ?loc (convert_exn ~env a) (convert_exn ~env b)
      | A.TyForall (v,t) ->
          let var = Var.make ~name:v in
          let env = MStr.add v (Ty.var ?loc var) env in
          Ty.forall ?loc var (convert_exn ~env t)

  let convert ~env ty =
    try E.return (convert_exn ~env ty)
    with e -> E.of_exn e
end

(** {2 Typed Term} *)
module type TERM = sig
  include NunTerm_intf.S

  module Ty : TYPE

  val loc : t -> loc option

  val ty : t -> Ty.t option
  (** Type of this term *)

  val sym : ?loc:loc -> ty:ty -> sym -> t
  val var : ?loc:loc -> ty:ty -> var -> t
  val app : ?loc:loc -> ty:ty -> t -> ty_arg:ty list -> t list -> t
  val fun_ : ?loc:loc -> ty:ty -> var -> ty_arg:ty -> t -> t
  val let_ : ?loc:loc -> var -> t -> t -> t
  val forall : ?loc:loc -> var -> ty_arg:ty -> t -> t
  val exists : ?loc:loc -> var -> ty_arg:ty -> t -> t
end

exception TypeError of string * loc option

let () = Printexc.register_printer
  (function
    | TypeError (msg, loc) ->
        Some (spf "type error: %s at %a" msg Loc.print_opt loc)
    | _ -> None
  )

module ConvertTerm(Term : TERM) = struct
  module Ty = Term.Ty
  module ConvertType = ConvertType(Ty)

  module Unif = NunTypeUnify.Make(Ty)

  type term_def =
    | Def of Term.t
    | Decl of Ty.t

  type term_env = {
    names: Var.t MStr.t; (* name -> variable, post-scoping *)
    defs : term_def Var.Map.t;  (* var -> type/definition *)
  }

  (* name -> definition *)

  type env = {
    ty: ConvertType.env;
    term: term_env;
  }

  let add_name ~env v var = {env with term={env.term with names=MStr.add v var env.term.names}}

  let add_def ~env v t = {env with term={env.term with defs=Var.Map.add v (Def t) env.term.defs}}

  let add_ty ~env v t = {env with term={env.term with defs=Var.Map.add v (Decl t) env.term.defs}}

  let add_ty_env ~env v ty = {env with ty=ConvertType.add_env ~env:env.ty v ty}

  (* obtain the type of a term *)
  let get_ty_ t = match Term.ty t with
    | None -> assert false
    | Some ty ->
        match Ty.deref ty with
        | None -> ty
        | Some ty' -> ty'

  let convert_exn ~env t = assert false

  let convert ~env t =
    try E.return (convert_exn ~env t)
    with e -> E.of_exn e
end

module type STATEMENT = sig
  include NunStatement_intf.S

  module T : TERM

  val loc : (_,_) t -> loc option

  val decl : ?loc:loc -> var -> T.Ty.t -> (_, T.Ty.t) t
  val def : ?loc:loc -> var -> T.t -> (T.t, _) t
  val axiom : ?loc:loc -> T.t -> (T.t,_) t
end

module ConvertStatement(St : STATEMENT) = struct
  module ConvertTerm = ConvertTerm(St.T)
  module ConvertType = ConvertTerm.ConvertType
  module T = St.T
  module Ty = T.Ty

  type t = (T.t, Ty.t) St.t

  type env = ConvertTerm.env

  let convert_exn ~env st =
    let loc = Loc.get_loc st in
    match Loc.get st with
    | A.Decl (v, ty) ->
        let var = Var.make ~name:v in
        let env = ConvertTerm.add_name ~env v var in
        let ty = ConvertType.convert_exn ~env:env.ConvertTerm.ty ty in
        let env = ConvertTerm.add_ty ~env var ty in
        St.decl ?loc var ty, env
    | A.Def ((v, ty_opt), t) ->
        let var = Var.make ~name:v in
        let env = ConvertTerm.add_name ~env v var in
        (* infer type for t *)
        let t = ConvertTerm.convert_exn ~env t in
        let env = ConvertTerm.add_def ~env var t in
        (* unify with [ty_opt] if present *)
        CCOpt.iter
          (fun ty ->
            let ty = ConvertType.convert_exn ~env:env.ConvertTerm.ty ty in
            ConvertTerm.Unif.unify_exn ty (ConvertTerm.get_ty_ t)
          ) ty_opt;
        St.def ?loc var t, env
    | A.Axiom t ->
        (* infer type for t *)
        let t = ConvertTerm.convert_exn ~env t in
        (* be sure it's a proposition *)
        ConvertTerm.Unif.unify_exn (ConvertTerm.get_ty_ t) ConvertType.prop;
        St.axiom ?loc t, env

  let convert ~env st =
    try E.return (convert_exn ~env st)
    with e -> E.of_exn e

  let convert_list_exn ~env l =
    let rec aux acc ~env l = match l with
      | [] -> List.rev acc, env
      | st :: l' ->
          let st, env = convert_exn ~env st in
          aux (st :: acc) ~env l'
    in
    aux [] ~env l

  let convert_list ~env st =
    try E.return (convert_list_exn ~env st)
    with e -> E.of_exn e
end
