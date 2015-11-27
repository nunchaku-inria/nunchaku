(* This file is free software, part of nunchaku. See file "license" for more details. *)

type 'a printer = Format.formatter -> 'a -> unit

type 't t = ('t * 't) list

let map ~f m = CCList.map (fun (x,y) -> f x, f y) m

let fpf = Format.fprintf

let print pt out m =
  let pp_pair out (t,u) = fpf out "@[<hv2>@[%a@]@ ->@ @[%a@]@]" pt t pt u in
  Format.fprintf out "@[<v>%a@]"
    (CCFormat.list ~start:"" ~stop:"" ~sep:"" pp_pair) m
