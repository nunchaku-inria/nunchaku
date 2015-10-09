
(* This file is free software, part of nunchaku. See file "license" for more details. *)

type 'a sequence = ('a -> unit) -> unit
type 'a or_error = [`Ok of 'a | `Error of string]

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

let debugf ?(section=Section.root) l msg =
  if l <= Section.cur_level section
    then (
      let now = Time.total () in
      if section == Section.root
        then Format.fprintf debug_fmt_ "@[<hov 3>%.3f[]@ " now
        else Format.fprintf debug_fmt_ "@[<hov 3>%.3f[%s]:@ "
          now section.Section.full_name;
        Format.kfprintf
          (fun fmt -> Format.fprintf fmt "@]@.")
          debug_fmt_ msg
    ) else Format.ifprintf debug_fmt_ msg

(** {2 Misc} *)

exception NotImplemented of string

let () = Printexc.register_printer
  (function
    | NotImplemented s -> Some ("feature `" ^ s ^ "` is not implemented")
    | _ -> None
  )

let not_implemented feat = raise (NotImplemented feat)

let err_of_exn e =
  let msg = Printexc.to_string e in
  let trace = Printexc.get_backtrace () in
  CCError.fail (msg ^ "\n" ^ trace)

let exn_ksprintf ~f fmt =
  let buf = Buffer.create 32 in
  let out = Format.formatter_of_buffer buf in
  Format.kfprintf
    (fun _ -> Format.pp_print_flush out (); raise (f (Buffer.contents buf)))
    out fmt

