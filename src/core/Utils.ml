
(* This file is free software, part of nunchaku. See file "license" for more details. *)

type 'a sequence = ('a -> unit) -> unit
type 'a or_error = ('a, string) CCResult.t

module Time = struct
  (** Time elapsed since initialization of the program, and time of start *)
  let total, start =
    let start = Unix.gettimeofday () in
    (function () ->
      let stop = Unix.gettimeofday () in
      stop -. start),
    (function () -> start)
end

(** {2 Debug} *)

(** Debug section *)
module Section = struct
  let null_level = -1 (* absence of level *)
  type t = {
    descr : descr;
    mutable full_name : string;
    mutable level : int;
  }
  and descr =
    | Root
    | Sub of string * t * t list  (* name, parent, inheriting *)

  let root={descr=Root; full_name=""; level=0; }

  (* computes full name of section *)
  let compute_full_name s =
    let buf = Buffer.create 15 in
    let rec add s = match s.descr with
      | Root -> true
      | Sub (name, parent, _) ->
          let parent_is_root = add parent in
          if not parent_is_root then Buffer.add_char buf '.';
          Buffer.add_string buf name;
          false
    in
    ignore (add s);
    Buffer.contents buf

  let full_name s = s.full_name

  (* full name -> section *)
  let section_table = Hashtbl.create 15

  let set_debug s i = assert (i>=0); s.level <- i
  let clear_debug s = s.level <- null_level
  let get_debug s =
    if s.level=null_level then None else Some s.level

  let make ?(parent=root) ?(inheriting=[]) name =
    if name="" then invalid_arg "Section.make: empty name";
    let sec = {
      descr=Sub(name, parent, inheriting);
      full_name="";
      level=null_level;
    } in
    let name' = compute_full_name sec in
    try
      Hashtbl.find section_table name'
    with Not_found ->
      (* new section! register it, add an option to set its level *)
      sec.full_name <- name';
      Hashtbl.add section_table name' sec;
      sec

  let iter yield =
    yield ("", root);
    Hashtbl.iter (fun name sec -> yield (name,sec)) section_table

  (* recursive lookup, with inheritance from parent *)
  let rec cur_level_rec s =
    if s.level = null_level
    then match s.descr with
      | Root -> 0
      | Sub (_, parent, []) -> cur_level_rec parent
      | Sub (_, parent, [i]) -> max (cur_level_rec parent) (cur_level_rec i)
      | Sub (_, parent, inheriting) ->
          List.fold_left
            (fun m i -> max m (cur_level_rec i))
            (cur_level_rec parent) inheriting
    else s.level

  (* inlinable function *)
  let cur_level s =
    if s.level = null_level
      then cur_level_rec s
      else s.level
end

let set_debug = Section.set_debug Section.root
let get_debug () = Section.root.Section.level

let debug_fmt_ = Format.err_formatter
let debug_lock_ = Mutex.create()

let debugf_real lock section msg k =
  if lock then Mutex.lock debug_lock_;
  let now = Time.total () in
  if section == Section.root
  then Format.fprintf debug_fmt_ "@[<hov 3>@{<Black>%.3f[]@}@ " now
  else Format.fprintf debug_fmt_ "@[<hov 3>@{<Black>%.3f[%s]@}@ "
    now section.Section.full_name;
  try
    k (Format.kfprintf
        (fun fmt -> Format.fprintf fmt "@]@."; if lock then Mutex.unlock debug_lock_)
        debug_fmt_ msg)
  with e ->
    if lock then Mutex.unlock debug_lock_;
    raise e

(* inlinable function *)
let debugf ?(lock=false) ?(section=Section.root) l msg k =
  if l <= Section.cur_level section
  then debugf_real lock section msg k

let debug ?lock ?section l msg = debugf ?lock ?section l "%s" (fun k->k msg)

module Callback = struct
  type callback_id = int

  type 'a callback = Nil | Cons of callback_id * 'a * 'a callback

  type 'a t = {
    mutable lst: 'a callback;
  }

  let create () = {lst=Nil}

  let count_ = ref 0

  let register t ~f =
      let id = !count_ in
      incr count_;
      t.lst <- Cons (id, f, t.lst);
      id

  let rec remove_rec_ l id = match l with
    | Nil -> Nil
    | Cons (id', f, l') ->
        if id=id' then l' else Cons (id', f, remove_rec_ l' id)

  let remove t ~id = t.lst <- remove_rec_ t.lst id

  let rec iter_rec_ f l = match l with
    | Nil -> ()
    | Cons (_, x, l') -> f x; iter_rec_ f l'

  let iter t ~f = iter_rec_ f t.lst

  let call1 t x = iter_rec_ (fun f -> f x) t.lst
  let call2 t x y = iter_rec_ (fun f -> f x y) t.lst
end

(** {2 Vector} *)

let vec_fold_map f acc v =
  let v' = CCVector.create () in
  let acc = CCVector.fold
    (fun acc x ->
      let acc, y = f acc x in
      CCVector.push v' y;
      acc
    ) acc v
  in
  acc, v'

(** {2 Lists} *)

let fold_mapi ~f ~x:acc l =
  let rec aux f acc i l = match l with
    | [] -> acc, []
    | x :: tail ->
        let acc, y = f i acc x in
        let acc, tail' = aux f acc (i+1) tail in
        acc, y :: tail'
  in
  aux f acc 0 l

let fold_map f acc l = fold_mapi ~f:(fun _ -> f) ~x:acc l

let filteri f l =
  let rec aux i = function
    | [] -> []
    | x :: tl ->
        let tl' = aux (i+1) tl in
        if f i x then x::tl' else tl'
  in
  aux 0 l

let singleton_if check ~f x = if check then [f x] else []

(** {2 Arg} *)

let arg_choice l f =
  let pick s =
    let s = s |> String.trim |> String.lowercase in
    try f (List.assoc s l)
    with Not_found -> assert false
  in
  Arg.Symbol (List.map fst l, pick)

(** {2 Warnings} *)

type warning =
  | Warn_overlapping_match
  | Warn_model_parsing_error

let pp_warn out = function
  | Warn_overlapping_match -> CCFormat.string out "overlapping pattern-match"
  | Warn_model_parsing_error -> CCFormat.string out "error when parsing model"

(* list of enabled warnings *)
let warnings_ =
  ref
    [ Warn_model_parsing_error ]

let is_warning_enabled w = List.mem w !warnings_

let toggle_warning w b =
  if b && not (is_warning_enabled w)
    then warnings_ := w :: !warnings_
  else if not b && is_warning_enabled w
    then warnings_ := List.filter (fun w' -> w<>w') !warnings_;
  ()

let warningf w msg =
  if is_warning_enabled w
  then (
    Format.eprintf "@[<2>[@{<yellow>Warning@} %a:@ " pp_warn w;
    Format.kfprintf
      (fun out ->
        Format.fprintf out "]@]@.";
        ())
      Format.err_formatter msg
  ) else Format.ikfprintf (fun _ -> ()) Format.err_formatter msg

let warning b msg = warningf b "%s" msg

let enable_warn_ w () = toggle_warning w true
let options_warnings_ =
  [ "--warn-overlapping-match"
      , Arg.Unit (enable_warn_ Warn_overlapping_match)
      , " enable warning on overlapping cases of pattern-matching"
  ; "-W1"
      , Arg.Bool (toggle_warning Warn_overlapping_match)
      , " <bool>: enable/disable --warn-overlapping-match"
  ; "-W2"
      , Arg.Bool (toggle_warning Warn_model_parsing_error)
      , " <bool>: enable/disable warnings on model parsing errors"
  ]

(** {2 Misc} *)

exception NotImplemented of string

let pp_seq ?(sep=" ") p = CCFormat.seq ~start:"" ~stop:"" ~sep p
let pp_list ?(sep=" ") p = CCFormat.list ~start:"" ~stop:"" ~sep p

(* print error prefix *)
let pp_error_prefix out () = Format.fprintf out "@{<Red>Error@}: "

let err_sprintf fmt =
  CCFormat.ksprintf fmt
    ~f:(fun s -> CCFormat.sprintf "@[<2>%a%s@]" pp_error_prefix () s)

let () = Printexc.register_printer
  (function
    | NotImplemented s ->
        Some (CCFormat.sprintf "%a feature `%s` is not implemented" pp_error_prefix () s)
    | _ -> None
  )

let not_implemented feat = raise (NotImplemented feat)

let err_of_exn e =
  let trace = Printexc.get_backtrace () in
  let msg = CCFormat.sprintf "%s\n%s" (Printexc.to_string e) trace in
  CCResult.fail msg

let exn_ksprintf ~f fmt =
  let buf = Buffer.create 32 in
  let out = Format.formatter_of_buffer buf in
  Format.fprintf out "@[<2>";
  Format.kfprintf
    (fun _ -> Format.fprintf out "@]@?"; raise (f (Buffer.contents buf)))
    out fmt

let not_implementedf fmt = exn_ksprintf fmt ~f:not_implemented
let failwithf fmt = exn_ksprintf fmt ~f:failwith

let ignore_catch f x =
  try ignore (f x)
  with _ -> ()
