
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Pipeline of Transformations} *)

type 'a printer = 'a CCFormat.printer

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
  mutable on_input : ('a -> unit) list;
  mutable on_encoded : ('b -> unit) list;
  mutable on_decoded : ('d -> unit) list;
  print_state : (Format.formatter -> 'st -> unit) option;  (** Debugging *)
}

type ('a, 'b, 'c, 'd) transformation = ('a, 'b, 'c, 'd) t
(** Alias to {!t} *)

let make ?print ?(on_input=[])
?(on_encoded=[]) ?(on_decoded=[]) ~name ~encode ~decode () =
  Ex {
    name;
    encode;
    decode;
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
  let print out t =
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
