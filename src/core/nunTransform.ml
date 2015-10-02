
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Pipeline of Transformations} *)

type 'a lazy_list = unit -> [`Nil | `Cons of 'a * 'a lazy_list]
(** A lazy list of values of type ['a] *)

(** {2 Single Transformation} *)

(** Transformation of ['a] to ['b]. The transformation make choices by
    lazily returning several values. It is also allowed to store data
    in a internal "state" type, to be able to transform back later. *)
type ('a, 'b) t = Ex : ('a, 'b, 'st) inner -> ('a, 'b) t

(** Transformation with explicit hidden state *)
and ('a, 'b, 'st) inner = {
  name : string; (** informal name for the transformation *)
  encode : 'a -> ('b * 'st) lazy_list;
  decode : 'st -> 'b -> 'a;
  print_state : (Format.formatter -> 'st -> unit) option;  (** Debugging *)
}

type ('a, 'b) transformation = ('a, 'b) t
(** Alias to {!t} *)

(** {2 Pipeline of Transformations}

    Allows chaining the transformations in a type-safe way *)

module Pipe = struct
  type ('a, 'b) t =
    | Id : ('a, 'a) t  (** no transformation *)
    | Comp : ('a, 'b) transformation * ('b, 'c) t -> ('a, 'c) t

  let id = Id
  let compose a p = Comp (a, p)
end

let rec run
  : type a b. pipe:(a,b) Pipe.t -> a -> (b * (b -> a)) lazy_list
  = fun ~pipe x -> match pipe with
  | Pipe.Id -> CCKList.return (x, fun x->x)
  | Pipe.Comp (Ex trans, pipe') ->
      let open CCKList in
      trans.encode x
      >>= fun (y, st) ->
      run ~pipe:pipe' y
      >|= fun (y', conv_back) ->
      let conv_back' x = trans.decode st (conv_back x) in
      y', conv_back'


