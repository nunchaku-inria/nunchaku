
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Encode Cardinality Constraints into Formulas} *)

module TI = TermInner

module type S = sig
  module T : TermInner.S

  type term = T.t
  type ty = T.t

  val encode_max_card : ty -> int -> term

  val encode_min_card : ty -> int -> term
end

module Make(T : TermInner.S) : S with module T = T = struct
  module T = T
  module U = TI.Util(T)

  type term = T.t
  type ty = T.t

  let encode_max_card ty n : term =
    let xs =
      CCList.init n (fun i -> Var.makef ~ty "x_%d" i)
    and y =
      Var.make ~name:"y" ~ty
    in
    let form_y_belongs_xs =
      U.forall y
        (U.or_
           (List.map (fun x -> U.eq (U.var x) (U.var y)) xs))
    in
    U.exists_l xs form_y_belongs_xs

  (* the type of [pred] has at least [n] elements, return list of axiom
     [exists x1...xn. pred x_i & xi != xj] *)
  let encode_min_card ty n : term =
    let xs =
      CCList.init n
        (fun i -> Var.makef ~ty "x_%d" i)
    in
    let pairwise_distinct =
      CCList.diagonal xs
      |> List.map (fun (x1,x2) -> U.neq (U.var x1) (U.var x2))
    in
    U.exists_l xs
      (U.and_ pairwise_distinct)
end
