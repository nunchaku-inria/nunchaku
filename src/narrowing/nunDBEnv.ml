
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Environment for De Bruijn indices} *)

type 'a t= {
  len : int;
  lst : 'a list;
}

let cons x {len;lst} = {len=len+1; lst=x::lst}
let cons_l l {len;lst} = {len=len+List.length l; lst=l@lst}
let nil = {len=0;lst=[];}
let length x = x.len
let is_empty x = x.len = 0

let to_list x = x.lst
let of_list lst = {len=List.length lst;lst}

let make ~len lst =
  assert (List.length lst = len);
  {lst;len}

let make_unsafe ~len lst = {len;lst}

let map f {len;lst} = {len; lst=List.map f lst}
let append_l {len;lst} l = {len=len+List.length l; lst=lst@l}

let nth l i = assert (i<l.len); List.nth l.lst i

let remove i {len;lst} =
  let rec aux c lst = match lst with
    | []        -> assert false
    | x::lst'   -> if c==0 then lst' else x::(aux (c-1) lst')
  in
  {len=len-1; lst=aux i lst}
