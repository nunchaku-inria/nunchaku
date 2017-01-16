
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Builtins} *)

module P = Precedence

type id = ID.t

let fpf = Format.fprintf

type +'a guard = {
  asserting: 'a list; (* postconditions, to be enforced *)
}

let empty_guard = {asserting=[]}

let map_guard f g =
  { asserting = List.map f g.asserting; }

let merge_guard g1 g2 =
  { asserting = List.rev_append g1.asserting g2.asserting; }

let pp_guard pterm out g: unit =
  let pp_case name out l = match l with
    | [] -> ()
    | _::_ ->
      fpf out "@ @[<2>%s@ @[<hv>%a@]@]" name
        (CCFormat.list ~start:"" ~stop:"" ~sep:" && " pterm) l
  in
  Format.fprintf out "%a"
    (pp_case "asserting") g.asserting

type 'a t =
  [ `True
  | `False
  | `Not of 'a
  | `Or of 'a list
  | `And of 'a list
  | `Imply of 'a * 'a
  | `Ite of 'a * 'a * 'a
  | `Eq of 'a * 'a
  | `DataTest of id (** Test whether [t : tau] starts with given constructor *)
  | `DataSelect of id * int (** Select n-th argument of given constructor *)
  | `Undefined_self of id * 'a (** Undefined case. argument=the undefined term *)
  | `Undefined_atom of id * 'a (** Undefined term (name+type) *)
  | `Unparsable of 'a (** could not parse model properly. Param=ty *)
  | `Guard of 'a * 'a guard (** term + some boolean conditions *)
  ]

let prec : _ t -> Precedence.t = function
  | `True
  | `False
  | `DataSelect _
  | `DataTest _
  | `Undefined_atom _ -> P.Bot
  | `Eq _ -> P.Eq
  | `Not _ -> P.Not
  | `Imply _
  | `Or _ -> P.Or
  | `And _ -> P.And
  | `Guard _ -> P.Guard
  | `Undefined_self _ -> P.App
  | _ -> P.Top

let rec print_infix_list pterm s out l = match l with
  | [] -> assert false
  | [t] -> pterm out t
  | t :: l' ->
    fpf out "@[%a@]@ %s %a"
      pterm t s (print_infix_list pterm s) l'

let pp pterm out : _ t -> unit = function
  | `True -> CCFormat.string out "true"
  | `False -> CCFormat.string out "false"
  | `Not x -> fpf out "@[<2>~@ %a@]" pterm x
  | `Or l ->
    fpf out "@[<hv>%a@]" (print_infix_list pterm "||") l
  | `And l ->
    fpf out "@[<hv>%a@]" (print_infix_list pterm "&&") l
  | `Imply (a,b) -> fpf out "@[@[%a@]@ @[<2>=>@ @[%a@]@]@]" pterm a pterm b
  | `Eq (a,b) ->
    fpf out "@[<hv>%a@ @[<hv>=@ %a@]@]" pterm a pterm b
  | `Ite (a,b,c) ->
    fpf out "@[<hv>@[<2>if@ %a@]@ @[<2>then@ %a@]@ @[<2>else@ %a@]@]"
      pterm a pterm b pterm c
  | `DataTest id -> fpf out "is-%s" (ID.name id)
  | `DataSelect (id, n) ->
    fpf out "select-%s-%d" (ID.name id) n
  | `Undefined_self (id,t) ->
    if !ID.print_undefined_id
    then fpf out "undefined_%d %a" (ID.id id) pterm t
    else fpf out "?__ %a" pterm t
  | `Undefined_atom (id,_ty) ->
    if !ID.print_undefined_id
    then fpf out "undefined_%d" (ID.id id)
    else CCFormat.string out "?__"
  | `Unparsable ty -> fpf out "@[<2>?__unparsable@ @[%a@]@]" pterm ty
  | `Guard (t, o) ->
    assert (o.asserting<>[]);
    fpf out "@[<hv>%a%a@]" pterm t (pp_guard pterm) o

let equal
  : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
  = fun eqterm a b -> match a, b with
    | `True, `True
    | `False, `False -> true
    | `Not a, `Not b -> eqterm a b
    | `Imply (a1,b1), `Imply (a2,b2) -> eqterm a1 a2 && eqterm b1 b2
    | `Or l1, `Or l2 -> CCList.equal eqterm l1 l2
    | `And l1, `And l2 -> CCList.equal eqterm l1 l2
    | `Ite(a1,b1,c1), `Ite(a2,b2,c2) ->
      eqterm a1 a2 && eqterm b1 b2 && eqterm c1 c2
    | `Eq(a1,b1), `Eq (a2,b2) -> eqterm a1 a2 && eqterm b1 b2
    | `DataTest id, `DataTest id' -> ID.equal id id'
    | `DataSelect (id, n), `DataSelect (id', n') -> n=n' && ID.equal id id'
    | `Undefined_self (a,t1), `Undefined_self (b,t2) -> ID.equal a b && eqterm t1 t2
    | `Undefined_atom (a,t1), `Undefined_atom (b,t2) -> ID.equal a b && eqterm t1 t2
    | `Unparsable t1, `Unparsable t2 -> eqterm t1 t2
    | `Guard (t1, g1), `Guard (t2, g2) ->
      List.length g1.asserting = List.length g2.asserting
      && eqterm t1 t2
      && List.for_all2 eqterm g1.asserting g2.asserting
    | `Guard _, _
    | `True, _ | `False, _ | `Ite _, _ | `Not _, _ | `Unparsable _, _
    | `Eq _, _ | `Or _, _ | `And _, _ | `Imply _, _
    | `DataSelect _, _ | `DataTest _, _
    | `Undefined_self _, _ | `Undefined_atom _, _ -> false

let map : f:('a -> 'b) -> 'a t -> 'b t
  = fun ~f b -> match b with
    | `True -> `True
    | `False -> `False
    | `And l -> `And (List.map f l)
    | `Imply (a,b) -> `Imply (f a, f b)
    | `Ite (a,b,c) -> `Ite (f a, f b, f c)
    | `Eq (a,b) -> `Eq (f a, f b)
    | `DataTest id -> `DataTest id
    | `Or l -> `Or (List.map f l)
    | `Not t -> `Not (f t)
    | `DataSelect (c,n) -> `DataSelect (c,n)
    | `Undefined_self (id, t) -> `Undefined_self (id, f t)
    | `Undefined_atom (id, t) -> `Undefined_atom (id, f t)
    | `Unparsable t -> `Unparsable (f t)
    | `Guard (t, g) ->
      let g' = map_guard f g in
      `Guard (f t, g')

let fold : f:('acc -> 'a -> 'acc) -> x:'acc -> 'a t -> 'acc
  = fun ~f ~x:acc b -> match b with
    | `True
    | `False
    | `DataTest _
    | `DataSelect _ -> acc
    | `Imply (a,b) -> f (f acc a) b
    | `Not t -> f acc t
    | `Or l
    | `And l -> List.fold_left f acc l
    | `Ite (a,b,c) -> f (f (f acc a) b) c
    | `Eq (a,b) -> f (f acc a) b
    | `Unparsable t
    | `Undefined_atom (_,t)
    | `Undefined_self (_,t) -> f acc t
    | `Guard (t, g) ->
      let acc = f acc t in
      List.fold_left f acc g.asserting

let fold2_l ~f ~fail ~x l1 l2 =
  if List.length l1=List.length l2
  then List.fold_left2 f x l1 l2
  else fail ()

let fold2 :
  f:('acc -> 'a -> 'b -> 'acc) -> fail:(unit -> 'acc) ->
  x:'acc -> 'a t -> 'b t -> 'acc
  = fun ~f ~fail ~x:acc b1 b2 -> match b1, b2 with
    | `True, `True
    | `False, `False -> acc
    | `Imply (a1,b1), `Imply (a2,b2) ->
      let acc = f acc a1 a2 in f acc b1 b2
    | `Not a, `Not b -> f acc a b
    | `And l1, `And l2 -> fold2_l ~f ~fail ~x:acc l1 l2
    | `Or l1, `Or l2 -> fold2_l ~f ~fail ~x:acc l1 l2
    | `DataTest i1, `DataTest i2 -> if ID.equal i1 i2 then acc else fail()
    | `DataSelect (i1,n1), `DataSelect (i2,n2) ->
      if n1=n2 && ID.equal i1 i2 then acc else fail()
    | `Ite (a1,b1,c1), `Ite(a2,b2,c2) ->
      let acc = f acc a1 a2 in
      let acc = f acc b1 b2 in
      f acc c1 c2
    | `Eq (a1,b1), `Eq (a2,b2) -> let acc = f acc a1 a2 in f acc b1 b2
    | `Undefined_self (i1,t1), `Undefined_self (i2,t2)
    | `Undefined_atom (i1,t1), `Undefined_atom (i2,t2) ->
      if ID.equal i1 i2 then f acc t1 t2 else fail()
    | `Unparsable t1, `Unparsable t2 -> f acc t1 t2
    | `Guard (t1, g1), `Guard (t2, g2)
      when List.length g1.asserting=List.length g2.asserting ->
      let acc = f acc t1 t2 in
      List.fold_left2 f acc g1.asserting g2.asserting
    | `Guard _, _
    | `True, _ | `False, _ | `Ite _, _ | `Not _, _ | `Unparsable _, _
    | `Eq _, _ | `Or _, _ | `And _, _ | `Imply _, _
    | `DataSelect _, _ | `DataTest _, _
    | `Undefined_self _, _ | `Undefined_atom _, _ -> fail()

let iter : ('a -> unit) -> 'a t -> unit
  = fun f b -> match b with
    | `True
    | `False
    | `DataTest _
    | `DataSelect _ -> ()
    | `Imply (a,b) -> f a; f b
    | `Not t -> f t
    | `And l
    | `Or l -> List.iter f l
    | `Ite (a,b,c) -> f a; f b; f c
    | `Eq (a,b) -> f a; f b
    | `Unparsable t
    | `Undefined_atom (_,t)
    | `Undefined_self (_,t) -> f t
    | `Guard (t,g) ->
      f t;
      List.iter f g.asserting;
      ()

let to_seq b f = iter f b

let to_sexp
  : ('a -> Sexp_lib.t) -> 'a t -> Sexp_lib.t
  = fun cterm t ->
    let str = Sexp_lib.atom and lst = Sexp_lib.list in
    match t with
      | `True -> str "true"
      | `False -> str "false"
      | `Not x -> lst [str "not"; cterm x]
      | `Or l -> lst (str "or" :: List.map cterm l)
      | `And l -> lst (str "and" :: List.map cterm l)
      | `Imply (a,b) -> lst [str "imply"; cterm a; cterm b]
      | `Eq (a,b) -> lst [str "="; cterm a; cterm b]
      | `Ite (a,b,c) -> lst [str "if"; cterm a; cterm b; cterm c]
      | `DataTest id -> str ("is-" ^ ID.to_string id)
      | `DataSelect (id, n) ->
        str (CCFormat.sprintf "select-%s-%d" (ID.name id) n)
      | `Undefined_self (id,t) ->
        lst [str "?__"; str (ID.to_string id); cterm t]
      | `Undefined_atom _ -> str "?__"
      | `Unparsable ty ->
        lst [str "?__unparsable"; cterm ty]
      | `Guard _ -> assert false (* TODO *)
