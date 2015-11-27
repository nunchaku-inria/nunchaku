
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Statements with Locations} *)

module Loc = Location
module ID = ID
module Var = Var
module Statement = Statement
module Model = Model
module Signature = Signature
module Env = Env

type loc = Loc.t
type id = ID.t
type 'a printer = Format.formatter -> 'a -> unit
type 'a or_error = [`Ok of 'a | `Error of string]

let fpf = Format.fprintf

type 'a vec_ro = ('a, CCVector.ro) CCVector.t

module Metadata = struct
  type t = {
    incomplete: bool;
  }

  let default = {incomplete=false}
  let set_incomplete _ = {incomplete=true}
  let add_incomplete m b = {incomplete=m.incomplete||b}
end

type ('t, 'ty, 'inv) t = {
  statements : ('t, 'ty, 'inv) Statement.t vec_ro;
  metadata: Metadata.t;
}


let statements t = t.statements
let metadata t = t.metadata

let make ~meta statements = { metadata=meta; statements; }

let of_list ~meta l = make ~meta (CCVector.of_list l)

let map_statements ~f pb = {
  metadata=pb.metadata;
  statements=CCVector.map f pb.statements;
}

let fold_map_statements ~f ~x pb =
  let acc, statements = Utils.vec_fold_map f x pb.statements in
  let statements = CCVector.freeze statements in
  acc, { pb with statements }

let flat_map_statements ~f pb =
  let res = CCVector.create () in
  CCVector.iter
    (fun st ->
      let new_stmts = f st in
      List.iter (CCVector.push res) new_stmts
    ) pb.statements;
  let res = CCVector.freeze res in
  { metadata=pb.metadata; statements=res; }

let map_with ?(before=fun _ -> []) ?(after=fun _ -> []) ~term ~ty p = {
  metadata=p.metadata;
  statements=(
    let res = CCVector.create () in
    CCVector.iter
      (fun st ->
        let st' = Statement.map ~term ~ty st in
        CCVector.append_seq res (Sequence.of_list (before ()));
        CCVector.push res st';
        CCVector.append_seq res (Sequence.of_list (after ()));
      ) p.statements;
    CCVector.freeze res
  );
}

let map ~term ~ty pb = map_with ~term ~ty pb

module Print(P1 : TermInner.PRINT)(P2 : TermInner.PRINT) = struct
  module PStmt = Statement.Print(P1)(P2)

  let print out pb =
    fpf out "{@,%a@,}"
      (CCVector.print ~start:"" ~stop:"" ~sep:"" PStmt.print)
      pb.statements
end

exception IllFormed of string
(** Ill-formed problem *)

let () = Printexc.register_printer
  (function
    | IllFormed msg -> Some (Printf.sprintf "problem is ill-formed: %s" msg)
    | _ -> None
  )

let ill_formed_ msg = raise (IllFormed msg)
let ill_formedf_ msg = Utils.exn_ksprintf msg ~f:ill_formed_

let goal pb =
  let n = CCVector.length pb.statements in
  let rec aux acc i =
    if i=n
    then match acc with
      | Some g -> g
      | None -> ill_formed_ "no goal"
    else
      match CCVector.get pb.statements i with
      | {Statement.view=Statement.Goal g;_} -> aux (Some g) (i+1)
      | _ -> aux acc (i+1)
  in
  aux None 0

let signature ?(init=Signature.empty) pb =
  CCVector.fold
    (fun sigma st -> Signature.add_statement ~sigma st)
    init pb.statements

let env ?init:(env=Env.create()) pb =
  let module St = Statement in
  try
    CCVector.fold
      (fun env st -> Env.add_statement ~env st)
      env pb.statements
  with Env.InvalidDef _ as e ->
    ill_formedf_ "invalid env: %a" Env.pp_invalid_def_ e

module Res = struct
  type 't model = 't Model.t

  type 't t =
    | Unsat
    | Sat of 't model  (** model maps terms to values *)
    | Timeout

  let map ~f t = match t with
    | Unsat -> Unsat
    | Timeout -> Timeout
    | Sat model -> Sat (Model.map ~f model)

  let fpf = Format.fprintf

  let print pt out = function
    | Unsat -> fpf out "unsat"
    | Timeout -> fpf out "timeout"
    | Sat m ->
        fpf out "@[<2>sat {@,%a}@]" (Model.print pt) m
end
