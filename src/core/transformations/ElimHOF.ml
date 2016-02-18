
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Elimination of Higher-Order Functions} *)

module TI = TermInner

let name = "elim_hof"
let section = Utils.Section.make name

type 'a inv = <ty:[`Mono]; eqn:'a; ind_preds: [`Absent]>

module Make(T : TI.S) = struct
  module U = TI.Util(T)
  module P = TI.Print(T)

  type term = T.t
  type decode_state = unit (* TODO *)

  (** {2 Encoding} *)

  let elim_hof pb = pb, ()  (* TODO *)

  (** {2 Decoding} *)

  let decode_model ~state:_ m = m  (* TODO *)

  (** {2 Pipe} *)

  let pipe_with ~decode ~print =
    let on_encoded = if print
      then
        let module PPb = Problem.Print(P)(P) in
        [Format.printf "@[<v2>after elimination of HOF: %a@]@." PPb.print]
      else []
    in
    Transform.make1
      ~on_encoded
      ~name
      ~encode:(fun p ->
        let p, state = elim_hof p in
        p, state
      )
      ~decode
      ()

  let pipe ~print =
    let decode state m = decode_model ~state m in
    pipe_with ~print ~decode

end



