
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
  include NunType_intf.S

  val loc : t -> loc option

  val deref : t -> t option

  val bind : var:t -> t -> unit
  (** [bind ~var t] binds the variable [var] to [t].
      @raise Invalid_argument if [var] is not a variable or if [var]
        is already bound *)

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
  type env = unit (* TODO *)

  let convert ~env t = assert false (* TODO *)
end
