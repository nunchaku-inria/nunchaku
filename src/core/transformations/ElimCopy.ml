
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Eliminate Copy Types} *)

module TI = TermInner

type ('a,'b) inv = <eqn:'a; ind_preds:'b; ty:[`Mono]>

module Make(T : TI.S) = struct
  module U = TI.Util(T)
  module P = TI.Print(T)

  type term = T.t

  let elim pb = pb (* TODO *)

  let pipe ~print =
    let on_encoded = if print
      then
        let module Ppb = Problem.Print(P)(P) in
        [Format.printf "@[<v2>after elimination of copy types:@ %a@]@." Ppb.print]
      else []
    in
    Transform.make1
      ~name:"elim_copy"
      ~on_encoded
      ~encode:(fun pb -> elim pb, ())
      ~decode:(fun () x -> x)
      ()
end
