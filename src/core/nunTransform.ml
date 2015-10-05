
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Pipeline of Transformations} *)

type 'a lazy_list = unit -> [`Nil | `Cons of 'a * 'a lazy_list]
(** A lazy list of values of type ['a] *)

(** {2 Single Transformation} *)

(** Transformation of ['a] to ['b]. The transformation make choices by
    lazily returning several values. It is also allowed to store data
    in a internal "state" type, to be able to transform back later. *)
(** Transformation with explicit hidden state *)
type ('a, 'b, 'c, 'd) t = Ex : ('a, 'b, 'c, 'd, 'st) inner -> ('a, 'b, 'c, 'd) t

and ('a, 'b, 'c, 'd, 'st) inner = {
  name : string; (** informal name for the transformation *)
  encode : 'a -> ('b * 'st) lazy_list;
  decode : 'st -> 'c -> 'd;
  mutable on_encoded : ('b -> unit) list;
  print_state : (Format.formatter -> 'st -> unit) option;  (** Debugging *)
}

type ('a, 'b, 'c, 'd) transformation = ('a, 'b, 'c, 'd) t
(** Alias to {!t} *)

let make ?print ?(name="<trans>") ~encode ~decode = Ex {
  name;
  encode;
  decode;
  on_encoded=[];
  print_state=print;
}

let on_encoded (Ex tr) ~f =
  tr.on_encoded <- f :: tr.on_encoded

(** {2 Pipeline of Transformations}

    Allows chaining the transformations in a type-safe way *)

module Pipe = struct
  type ('a, 'b, 'c, 'd) t =
    | Id : ('a, 'a, 'c, 'c) t  (** no transformation *)
    | Comp : ('a, 'b, 'd, 'e) transformation * ('b, 'b2, 'c, 'd) t -> ('a, 'b2, 'c, 'e) t

  let id = Id
  let compose a p = Comp (a, p)
end

let callbacks_ l x =
  List.iter
    (fun f ->
      try f x with _ -> ()
    ) l

let rec run
  : type a b c d. pipe:(a,b,c,d) Pipe.t -> a -> (b * (c -> d)) lazy_list
  = fun ~pipe x -> match pipe with
  | Pipe.Id -> CCKList.return (x, fun x->x)
  | Pipe.Comp (Ex trans, pipe') ->
      let open CCKList in
      trans.encode x
      >>= fun (y, st) ->
      callbacks_ trans.on_encoded y;
      run ~pipe:pipe' y
      >|= fun (y', conv_back) ->
      let conv_back' x = trans.decode st (conv_back x) in
      y', conv_back'


