(* This file is free software, part of nunchaku. See file "license" for more details. *)

type 'a printer = Format.formatter -> 'a -> unit

type 't t = {
  terms: ('t * 't) list;  (* term -> its interpretation *)
  finite_types: ('t * 't list) list;  (* type -> finite domain *)
}

let empty = {
  terms=[];
  finite_types=[];
}

let make ?(finite_types=[]) terms = {terms; finite_types; }

let add t pair = {t with terms = pair :: t.terms; }

let add_finite_type t ty dom =
  {t with finite_types = (ty, dom) :: t.finite_types; }

let map ~f m = {
  terms=CCList.map (fun (x,y) -> f x, f y) m.terms;
  finite_types=List.map (fun (ty,l) -> f ty, List.map f l) m.finite_types;
}

let filter_map ~terms ~finite_types m = {
  terms = CCList.filter_map terms m.terms;
  finite_types = CCList.filter_map finite_types m.finite_types;
}

let iter ~terms ~finite_types m =
  List.iter terms m.terms;
  List.iter finite_types m.finite_types;
  ()

let print pt out m =
  let fpf = Format.fprintf in
  let pp_pair out (t,u) = fpf out "@[<hv2>@[%a@]@ ->@ @[%a@]@]" pt t pt u in
  let pp_dom out (ty, dom) =
    fpf out "@[<h>@[%a@] -> {@[<hv>%a@]}@]"
      pt ty (CCFormat.list ~start:"" ~stop:"" ~sep:", " pt) dom
  in
  let pp_types out m = match m with
    | [] -> ()
    | _::_ ->
      Format.fprintf out "@[<hv2>types {@,%a@,}@]"
        (CCFormat.list ~start:"" ~stop:"" ~sep:"" pp_dom) m
  in
  Format.fprintf out "@[<hv2>model {@,terms {@,@[<hv2>%a@]@,}@,%a@]@,}@]"
    (CCFormat.list ~start:"" ~stop:"" ~sep:"" pp_pair) m.terms
    pp_types m.finite_types
