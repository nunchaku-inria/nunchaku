
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Types} *)

type id = NunID.t
type 'a var = 'a NunVar.t
type 'a printer = Format.formatter -> 'a -> unit

type ('a, 'inv) view =
  | Builtin of NunBuiltin.Ty.t (** Builtin type *)
  | Const of id
  | Var :
      'a var (** Constant or bound variable *)
      -> ('a, <poly:[`Poly];..>) view
  | Meta :
      'a NunMetaVar.t (** Meta-variable, used for unification *)
      -> ('a, <meta: [`Meta];..>) view
  | App of 'a * 'a list
  | Arrow of 'a * 'a
  | Forall :   (** Polymorphic type *)
      'a var
      * 'a
      -> ('a, <poly: [`Poly];..>) view

type ('t, 'inv) repr = ('t -> ('t, 'inv) view)
(** A representation of types with concrete type ['t], and invariants
    ['inv].
    The view function must follow {!deref} pointers *)

val view : repr:('t, 'inv) repr -> 't -> ('t, 'inv) view

(** {2 Utils} *)

val is_Type : repr:('t, 'inv) repr -> 't -> bool
(** type == Type? *)

val returns_Type : repr:('t,'inv) repr -> 't -> bool
(** type == forall ... -> ... -> ... -> Type? *)

val returns : repr:('t,'inv) repr -> 't -> 't
(** follow forall/arrows to get return type.  *)

val is_Kind : repr:('t,_) repr -> 't -> bool
(** type == Kind? *)

val to_seq : repr:('t,'inv) repr -> 't -> 't Sequence.t

(** {2 Type packed with its representation} *)

type packed = Packed : 't * ('t, _) repr -> packed

val pack : repr:('t, _) repr -> 't -> packed

(** {2 Print Types} *)
type 't print_funs = {
  print: 't printer;
  print_in_app: 't printer;
  print_in_arrow: 't printer;
}

val mk_print : repr:('t,_) repr -> 't print_funs
(** Make printers for this type *)

val print: repr:('t,_) repr -> 't printer
val print_in_app: repr:('t,_) repr -> 't printer
val print_in_arrow: repr:('t,_) repr -> 't printer
