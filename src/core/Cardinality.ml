
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Cardinalities} *)

module Z = struct
  type t = Big_int.big_int
  let zero = Big_int.zero_big_int
  let of_int = Big_int.big_int_of_int
  let one = of_int 1
  let sign = Big_int.sign_big_int
  let equal = Big_int.eq_big_int
  let to_int n =
    try Some (Big_int.int_of_big_int n)
    with _ -> None
  let to_string = Big_int.string_of_big_int
  let pp_print out x = CCFormat.string out (to_string x)
  let compare = Big_int.compare_big_int
  let hash x = Hashtbl.hash (to_string x)
  let (+) = Big_int.add_big_int
  let ( * ) = Big_int.mult_big_int
end

type t =
  | Exact of Z.t

  | QuasiFiniteGEQ of Z.t
  (** unknown, but ≥ 0. If all uninterpreted types are finite, then
            this is finite too *)

  | Infinite

  | Unknown
  (** Any value, we do not know *)

let (+) a b = match a, b with
  | Unknown, _
  | _, Unknown -> Unknown
  | QuasiFiniteGEQ a, (QuasiFiniteGEQ b | Exact b)
  | Exact a, QuasiFiniteGEQ b -> QuasiFiniteGEQ Z.(a+b)
  | Exact a, Exact b -> Exact Z.(a+b)
  | Infinite, _
  | _, Infinite -> Infinite (* even infinite+unknown = infinite *)

let zero = Exact Z.zero

let one = Exact Z.one
let of_int i = Exact (Z.of_int i)
let of_z i = Exact i
let quasi_finite_geq n = QuasiFiniteGEQ n
let quasi_finite_zero = QuasiFiniteGEQ Z.zero
let quasi_finite_nonzero = QuasiFiniteGEQ Z.one
let infinite = Infinite
let unknown = Unknown
let is_zero = function Exact z -> Z.sign z = 0 | _ -> false

let ( * ) a b = match a, b with
  | Unknown, _
  | _, Unknown -> Unknown
  | Exact x, _
  | _, Exact x when Z.sign x = 0 -> zero (* absorption by 0 *)
  | (QuasiFiniteGEQ z, _ | _, QuasiFiniteGEQ z) when Z.sign z = 0 ->
    quasi_finite_zero (* [0,∞] *)
  | Infinite, _
  | _, Infinite ->
    (* we know the other param is not 0 and does not contain 0 *)
    Infinite
  | Exact a, Exact b -> Exact Z.(a*b)
  | QuasiFiniteGEQ a, (Exact b | QuasiFiniteGEQ b)
  | Exact a, QuasiFiniteGEQ b -> QuasiFiniteGEQ Z.(a * b)  (* absorbs bounded *)

let sum = List.fold_left (+) zero
let product = List.fold_left ( * ) one

let equal a b = match a, b with
  | Unknown, Unknown -> true
  | QuasiFiniteGEQ a, QuasiFiniteGEQ b
  | Exact a, Exact b -> Z.equal a b
  | Infinite, Infinite -> true
  | Unknown, _
  | Infinite, _
  | QuasiFiniteGEQ _, _
  | Exact _, _ -> false

let hash = function
  | Exact x -> Z.hash x
  | QuasiFiniteGEQ z -> Hashtbl.hash (13, Z.hash z)
  | Unknown -> 13
  | Infinite -> 17
let hash_fun x = CCHash.int (hash x)

let print out = function
  | Unknown -> CCFormat.string out "<unknown>"
  | Exact x -> Z.pp_print out x
  | QuasiFiniteGEQ z -> Format.fprintf out "[%a,∞]" Z.pp_print z
  | Infinite -> CCFormat.string out "ω"
