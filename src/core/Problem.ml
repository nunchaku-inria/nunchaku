
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Statements with Locations} *)

module Loc = Location
module Metadata = ProblemMetadata

type loc = Loc.t
type id = ID.t
type 'a printer = Format.formatter -> 'a -> unit
type 'a to_sexp = 'a -> Sexp_lib.t
type 'a or_error = ('a, string) CCResult.t
type metadata = ProblemMetadata.t

let fpf = Format.fprintf

type ('t, 'ty) t = {
  statements : ('t, 'ty) Statement.t CCVector.ro_vector;
  metadata: Metadata.t;
}

let statements t = t.statements
let metadata t = t.metadata
let update_meta t f = { t with metadata = f t.metadata; }

let add_sat_means_unknown b t = update_meta t (Metadata.add_sat_means_unknown b)
let set_sat_means_unknown t = update_meta t Metadata.set_sat_means_unknown

let add_unsat_means_unknown b t = update_meta t (Metadata.add_unsat_means_unknown b)
let set_unsat_means_unknown t = update_meta t Metadata.set_unsat_means_unknown

let make ~meta statements = { metadata=meta; statements; }

let of_list ~meta l = make ~meta (CCVector.of_list l)

let iter_statements ~f pb = CCVector.iter f pb.statements

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
    let str_of_meta m =
      (if m.Metadata.sat_means_unknown then "(sat->?)" else "") ^
      (if m.Metadata.unsat_means_unknown then "(unsat->?)" else "")
    in
    fpf out "{%s@,%a@,}"
      (str_of_meta pb.metadata)
      (CCVector.print ~start:"" ~stop:"" ~sep:"" PStmt.print)
      pb.statements
end

module Convert(T1 : TermInner.REPR)(T2 : TermInner.BUILD) = struct
  module C = TermInner.Convert(T1)(T2)

  type ('a, 'b, 'c) inv = <eqn:'a; ind_preds:'b; ty: 'c>

  let convert pb = map ~term:C.convert ~ty:C.convert pb

  let pipe () =
    Transform.make
      ~name:"convert"
      ~encode:(fun pb -> convert pb, ())
      ~decode:(fun () x -> x)
      ()
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
  type (+'t,+'ty) t =
    | Unsat
    | Sat of ('t,'ty) Model.t
    | Unknown
    | Timeout
    | Out_of_scope
    | Error of exn

  let map_m ~f t =  match t with
    | Unsat -> Unsat
    | Timeout -> Timeout
    | Error e -> Error e
    | Unknown -> Unknown
    | Out_of_scope -> Out_of_scope
    | Sat m -> Sat (f m)

  let map ~term ~ty t =
    map_m t ~f:(Model.map ~term ~ty)

  let fpf = Format.fprintf

  let print_head out = function
    | Unsat -> fpf out "UNSAT"
    | Timeout -> fpf out "TIMEOUT"
    | Error e -> fpf out "ERROR %s" (Printexc.to_string e)
    | Unknown -> fpf out "UNKNOWN"
    | Out_of_scope -> fpf out "OUT_OF_SCOPE"
    | Sat _ -> fpf out "SAT"

  let print pt pty out = function
    | Unsat -> fpf out "UNSAT"
    | Timeout -> fpf out "TIMEOUT"
    | Error e -> fpf out "ERROR %s" (Printexc.to_string e)
    | Unknown -> fpf out "UNKNOWN"
    | Out_of_scope -> fpf out "OUT_OF_SCOPE"
    | Sat m ->
        fpf out "@[<hv>@[<v2>SAT: {@,@[<v>%a@]@]@,}@]" (Model.print pt pty) m

  let str = Sexp_lib.atom
  let lst = Sexp_lib.list

  let to_sexp ft fty : (_,_) t to_sexp = function
    | Unsat -> str "UNSAT"
    | Timeout -> str "TIMEOUT"
    | Error e -> lst [str "ERROR"; str (Printexc.to_string e)]
    | Unknown -> str "UNKNOWN"
    | Out_of_scope -> str "OUT_OF_SCOPE"
    | Sat m -> lst [str "SAT"; Model.to_sexp ft fty m]
end
