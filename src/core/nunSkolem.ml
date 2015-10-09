
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Skolemization} *)

module type S = sig
  module T1 : NunTerm_ho.VIEW
  module T2 : NunTerm_ho.S

  type state

  val create : unit -> state

  val convert_term : state:state -> T1.t -> T2.t

  val convert_problem :
    state:state ->
    (T1.t, T1.ty) NunProblem.t ->
    (T2.t, T2.ty) NunProblem.t

  val decode_model :
    state:state -> T2.t NunProblem.Model.t -> T2.t NunProblem.Model.t
end

module Make(T1 : NunTerm_ho.VIEW)(T2 : NunTerm_ho.S)
  : S with module T1 = T1 and module T2 = T2
= struct
  module T1 = T1
  module T2 = T2

  type state = unit (* TODO *)

  let create () = ()

  let convert_term ~state t = assert false (* TODO *)

  let convert_problem ~state pb = assert false (* TODO *)

  let decode_model ~state m = m (* TODO *)
end

let pipe (type a)(type b) ~print
(module T1 : NunTerm_ho.VIEW with type t = a)
(module T2 : NunTerm_ho.S with type t = b)
=
  let module S = Make(T1)(T2) in
  let on_encoded = if print
    then
      let module P = NunTerm_ho.Print(T2) in
      [Format.printf "@[<2>after Skolemization:@ %a@]@."
        (NunProblem.print P.print P.print_ty)]
    else []
  in
  NunTransform.make1
    ~name:"skolem"
    ~on_encoded
    ~encode:(fun pb ->
      let state = S.create() in
      let pb = S.convert_problem ~state pb in
      pb, state
    )
    ~decode:(fun state m -> S.decode_model ~state m)
    ()

