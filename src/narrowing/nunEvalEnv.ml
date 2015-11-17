
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Global and Local Environment for Evaluation} *)

module ID = NunID
module T = NunTermEval

type id = ID.t

type t = {
  consts: T.const ID.PerTbl.t; (* symbol -> definition *)  
}
let create() = {consts=ID.PerTbl.create 32; }
let find_exn ~env id = ID.PerTbl.find env.consts id
let find ~env id = try Some (find_exn ~env id) with Not_found -> None
let declare ~env c = {consts=ID.PerTbl.add env.consts c.T.const_id c}
