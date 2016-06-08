
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Statements with Locations} *)

module Loc = Location
module Metadata = ProblemMetadata

type loc = Loc.t
type id = ID.t
type 'a printer = Format.formatter -> 'a -> unit
type 'a to_sexp = 'a -> CCSexp.t
type 'a or_error = ('a, string) CCResult.t

let fpf = Format.fprintf

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
    | Fun

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
    ; Data, Present
    ; Match, Present
    ; Fun, Present
    ] |> M.of_list

  let update = M.add
  let of_list = M.of_list

  (* check that every pair [k,v in spec] is also in [t] *)
  let check t ~spec =
    M.for_all
      (fun k v -> match M.get k t with
         | None -> false
         | Some v' -> v=v')
      spec

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
    | Fun -> "fun"

  let print out (m:t) =
    let pp_k out x = CCFormat.string out (str_of_key x) in
    let pp_v out x = CCFormat.string out (str_of_value x) in
    fpf out "@[<hv>%a@]" (M.print ~start:"" ~stop:"" pp_k pp_v) m
end

type ('t, 'ty) t = {
  statements : ('t, 'ty) Statement.t CCVector.ro_vector;
  metadata: Metadata.t;
  features: Features.t;
}

let statements t = t.statements
let metadata t = t.metadata
let features t = t.features
let update_meta t f = { t with metadata = f t.metadata; }

let map_features ~f t = { t with features = f t.features; }

let check_features t ~spec =
  if not (Features.check ~spec t.features)
  then Utils.failwithf
      "@[<hv2>feature mismatch:@ expected @[%a@],@ got @[%a@]@]"
      Features.print spec Features.print t.features

let add_sat_means_unknown b t = update_meta t (Metadata.add_sat_means_unknown b)
let set_sat_means_unknown t = update_meta t Metadata.set_sat_means_unknown

let add_unsat_means_unknown b t = update_meta t (Metadata.add_unsat_means_unknown b)
let set_unsat_means_unknown t = update_meta t Metadata.set_unsat_means_unknown

let make ~features ~meta statements =
  { metadata=meta; statements; features; }

let of_list ~features ~meta l = make ~features ~meta (CCVector.of_list l)

let iter_statements ~f pb = CCVector.iter f pb.statements

let id_ x = x

let map_statements ?features:(fft=id_) ~f pb = {
  features=fft pb.features;
  metadata=pb.metadata;
  statements=CCVector.map f pb.statements;
}

let fold_map_statements ?features:(fft=id_) ~f ~x pb =
  let acc, statements = Utils.vec_fold_map f x pb.statements in
  let statements = CCVector.freeze statements in
  acc, { pb with statements; features=fft pb.features }

let flat_map_statements ?features:(fft=id_) ~f pb =
  let res = CCVector.create () in
  CCVector.iter
    (fun st ->
      let new_stmts = f st in
      List.iter (CCVector.push res) new_stmts
    ) pb.statements;
  let res = CCVector.freeze res in
  { features=fft pb.features;
    metadata=pb.metadata;
    statements=res;
  }

let map_with ?features:(fft=id_) ?(before=fun _ -> []) ?(after=fun _ -> []) ~term ~ty p = {
  metadata=p.metadata;
  features=fft p.features;
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

let map ?features ~term ~ty pb = map_with ?features ~term ~ty pb

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
    | Error of exn

  let map_m ~f t =  match t with
    | Unsat -> Unsat
    | Timeout -> Timeout
    | Error e -> Error e
    | Unknown -> Unknown
    | Sat m -> Sat (f m)

  let map ~term ~ty t =
    map_m t ~f:(Model.map ~term ~ty)

  let fpf = Format.fprintf

  let print_head out = function
    | Unsat -> fpf out "UNSAT"
    | Timeout -> fpf out "TIMEOUT"
    | Error e -> fpf out "ERROR %s" (Printexc.to_string e)
    | Unknown -> fpf out "UNKNOWN"
    | Sat _ -> fpf out "SAT"

  let print pt pty out = function
    | Unsat -> fpf out "UNSAT"
    | Timeout -> fpf out "TIMEOUT"
    | Error e -> fpf out "ERROR %s" (Printexc.to_string e)
    | Unknown -> fpf out "UNKNOWN"
    | Sat m ->
        fpf out "@[<hv>@[<v2>SAT: {@,@[<v>%a@]@]@,}@]" (Model.print pt pty) m

  let str = CCSexp.atom
  let lst = CCSexp.of_list

  let to_sexp ft fty : (_,_) t to_sexp = function
    | Unsat -> str "UNSAT"
    | Timeout -> str "TIMEOUT"
    | Error e -> lst [str "ERROR"; str (Printexc.to_string e)]
    | Unknown -> str "UNKNOWN"
    | Sat m -> lst [str "SAT"; Model.to_sexp ft fty m]
end
