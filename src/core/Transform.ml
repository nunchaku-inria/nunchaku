
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Pipeline of Transformations} *)

type 'a printer = 'a CCFormat.printer

(** {2 Features} *)

module Features = struct
  type value =
    | Present
    | Absent
    | Mono
    | Poly
    | Eqn_single
    | Eqn_nested
    | Eqn_app

  (* the various kind of features *)
  type key =
    | Ty
    | Eqn
    | If_then_else
    | Ind_preds
    | Match
    | Data
    | Codata
    | Fun (* lambdas *)
    | HOF (* any higher-order fun *)
    | Prop_args (* propositions as arguments to functions *)
    | Pseudo_prop (* some type with flag "pseudo-prop" *)
    | Copy
    | Partial_app_cstor (* partially applied cstors *)

  module M = CCMap.Make(struct
      type t = key
      let compare = Pervasives.compare
    end)

  type t = value M.t

  let empty = M.empty

  let full =
    [ Ty, Poly
    ; Eqn, Eqn_nested
    ; If_then_else, Present
    ; Ind_preds, Present
    ; Match, Present
    ; Data, Present
    ; Codata, Present
    ; Fun, Present
    ; HOF, Present
    ; Prop_args, Present
    ; Pseudo_prop, Absent
    ; Copy, Present
    ; Partial_app_cstor, Present
    ] |> M.of_list

  let update = M.add
  let update_l l = List.fold_right (fun (k,v) -> update k v) l
  let of_list l = M.of_list l

  type check_res =
    | Check_ok
    | Check_fail of key * value * value

  (* check that every pair [k,v in spec] is also in [t] *)
  let check t ~spec : check_res =
    let bad =
      M.to_list spec
      |> CCList.find_map
        (fun (k,v) -> match M.get k t with
           | None -> assert false
           | Some v' -> if v=v' then None else Some (k,v,v'))
    in
    match bad with
      | None -> Check_ok
      | Some (k,v,v') -> Check_fail (k,v,v')

  let str_of_value = function
    | Present -> "present"
    | Absent -> "absent"
    | Mono -> "mono"
    | Poly -> "poly"
    | Eqn_single -> "single"
    | Eqn_nested -> "nested"
    | Eqn_app -> "app"

  let str_of_key = function
    | Ty -> "ty"
    | Eqn -> "eqn"
    | If_then_else -> "ite"
    | Ind_preds -> "ind_preds"
    | Match -> "match"
    | Data -> "data"
    | Codata -> "codata"
    | Fun -> "fun"
    | HOF -> "hof"
    | Prop_args -> "prop_args"
    | Pseudo_prop -> "pseudo_prop"
    | Copy -> "copy"
    | Partial_app_cstor -> "partial_applied_cstors"

  let pp out (m:t) =
    let pp_pair out (k,v) =
      Format.fprintf out "%s -> %s" (str_of_key k) (str_of_value v)
    in
    Format.fprintf out "@[<hv>%a@]" (Utils.pp_seq pp_pair) (M.to_iter m)
end

(** {2 Single Transformation} *)

(** Transformation of ['a] to ['b]. The transformation make choices by
    lazily returning several values. It is also allowed to store data
    in a internal "state" type, to be able to transform back later. *)
type ('a, 'b, 'c, 'd) t = Ex : ('a, 'b, 'c, 'd, 'st) inner -> ('a, 'b, 'c, 'd) t

(** Transformation with explicit hidden state *)
and ('a, 'b, 'c, 'd, 'st) inner = {
  name : string; (** name for the transformation, used for debug, CLI options, etc. *)
  encode : 'a -> ('b * 'st);
  decode : 'st -> 'c -> 'd;
  input_spec : Features.t;
  map_spec : Features.t -> Features.t;
  mutable on_input : ('a -> unit) list;
  mutable on_encoded : ('b -> unit) list;
  mutable on_decoded : ('d -> unit) list;
  print_state : (Format.formatter -> 'st -> unit) option;  (** Debugging *)
}

type ('a, 'b, 'c, 'd) transformation = ('a, 'b, 'c, 'd) t
(** Alias to {!t} *)

let make
    ?print ?(on_input=[])
    ?(on_encoded=[]) ?(on_decoded=[]) ?(input_spec=Features.empty)
    ?(map_spec=fun x->x) ~name ~encode ~decode () =
  Ex {
    name;
    encode;
    decode;
    input_spec;
    map_spec;
    on_input;
    on_encoded;
    on_decoded;
    print_state=print;
  }

let backward ~name f =
  let decode () x = f x in
  make ~name ~encode:(fun x->x,()) ~decode ()

let nop () = make ~name:"nop" ~encode:(fun x->x,()) ~decode:(fun () y->y) ()

let on_input (Ex tr) ~f = tr.on_input <- f :: tr.on_input
let on_encoded (Ex tr) ~f = tr.on_encoded <- f :: tr.on_encoded

(** {2 Pipeline of Transformations}

    Allows chaining the transformations in a type-safe way *)

module Pipe = struct
  type ('a, 'b, 'c, 'd) t =
    | Id : ('a, 'a, 'c, 'c) t (** no transformation *)
    | Fail : ('a, 'b, 'c, 'd) t (** yields empty list *)
    | Flatten :
        ('a, 'b list, 'c, 'd) t ->
      ('a, 'b, 'c, 'd) t
    | Close :
        ('b1 -> ('c1 -> 'd) -> 'b2 * ('c2 -> 'd)) *
          ('a, 'b1, 'c1, 'd) t ->
      ('a, 'b2, 'c2, 'd) t
    | Comp :
        ('a, 'b, 'e, 'f) transformation *
          ('b, 'c, 'd, 'e) t ->
      ('a, 'c, 'd, 'f) t
    | Fork :
        ('a, 'b, 'c, 'd) t *
          ('a, 'b, 'c, 'd) t ->
      ('a, 'b, 'c, 'd) t

  let id = Id
  let fail = Fail
  let flatten = function
    | Fail -> Fail
    | p -> Flatten p
  let close ~f = function
    | Fail -> Fail
    | p -> Close (f,p)
  let compose a p = match p with
    | Fail -> Fail
    | _ -> Comp (a, p)
  let fork
    : type a b c d.
      (a, b, c, d) t ->
      (a, b, c, d) t ->
      (a, b, c, d) t
    = fun a b -> match a, b with
      | Fail, o
      | o, Fail -> o
      | Id, Id -> Id
      | _ -> Fork (a,b)
  let rec fork_l = function
    | [] -> Fail
    | [a] -> a
    | a :: b -> fork a (fork_l b)
  let (@@@) = compose
  let fork_comp l kont =
    fork_l (List.map (fun t -> t @@@ kont) l)

  let fpf = Format.fprintf
  let pp out t =
    let rec pp : type a b c d. (a,b,c,d) t printer
      = fun out t -> match t with
        | Id -> fpf out "id"
        | Fail -> fpf out "fail"
        | Flatten t -> fpf out "flatten {@[%a@]}" pp t
        | Close (_, pipe) -> fpf out "close {@[%a@]}" pp pipe
        | Comp (Ex tr, t') ->
          fpf out "@[%s ≡≡@ %a@]" tr.name pp t'
        | Fork (a,b) ->
          fpf out "fork @[<v>{ @[%a@]@,| @[%a@]@,}@]" pp a pp b
    in
    fpf out "@[%a@]" pp t

  let check_features_ ~name f ~spec = match Features.check ~spec f with
    | Features.Check_ok -> ()
    | Features.Check_fail (k,expected,actual) ->
      Utils.failwithf
        "@[<hv2>feature mismatch in transformation %s:@ \
         on feature %s, expected %s, got %s@ \
         features: @[%a@],@ state: @[%a@]@]"
        name (Features.str_of_key k)
        (Features.str_of_value expected) (Features.str_of_value actual)
        Features.pp spec Features.pp f

  let check p =
    let rec aux
      : type a b c d. Features.t -> (a,b,c,d) t -> unit
      = fun f p -> match p with
        | Id -> ()
        | Fail -> ()
        | Close (_, p') -> aux f p'
        | Flatten p' -> aux f p'
        | Comp (Ex tr, p') ->
          check_features_ f ~name:tr.name ~spec:tr.input_spec;
          aux (tr.map_spec f) p'
        | Fork (p1,p2) ->
          aux f p1;
          aux f p2
    in
    aux Features.full p
end

(* run callbacks on [x] *)
let callbacks_ l x = List.iter (fun f -> f x) l

let rec run
  : type a b c d. pipe:(a,b,c,d) Pipe.t -> a -> (b * (c -> d)) Lazy_list.t
  = fun ~pipe x ->
    let open Lazy_list.Infix in
    match pipe with
      | Pipe.Id -> Lazy_list.return (x, fun x->x)
      | Pipe.Fail -> Lazy_list.empty
      | Pipe.Flatten pipe' ->
        run ~pipe:pipe' x
        >>= fun (l, ret) ->
        (* yield each element of [l] separately *)
        Lazy_list.of_list l
        >|= fun y -> y, ret
      | Pipe.Close (f, pipe) ->
        let l = run ~pipe x in
        l >|= fun (y, back) ->
        f y back
      | Pipe.Comp (Ex trans, pipe') ->
        callbacks_ trans.on_input x;
        let y, st = trans.encode x in
        callbacks_ trans.on_encoded y;
        run ~pipe:pipe' y
        >|= fun (y', conv_back) ->
        let conv_back' x =
          let res = trans.decode st (conv_back x) in
          callbacks_ trans.on_decoded res;
          res
        in
        y', conv_back'
      | Pipe.Fork (a, b) ->
        Lazy_list.append (run ~pipe:a x) (run ~pipe:b x)
