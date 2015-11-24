(* This file is free software, part of nunchaku. See file "license" for more details. *)

module ID = NunID
module Stmt = NunStatement

type id = NunID.t

type 'ty t = 'ty NunID.Map.t

let empty = ID.Map.empty

let mem ~sigma id = ID.Map.mem id sigma
let find_exn ~sigma id = ID.Map.find id sigma
let find ~sigma id =
  try Some (find_exn ~sigma id)
  with Not_found -> None

let declare ~sigma id ty = ID.Map.add id ty sigma

let add_statement ~sigma st = match Stmt.view st with
  | Stmt.Decl (id,_,ty) -> declare ~sigma id ty
  | Stmt.Axiom (Stmt.Axiom_rec l) ->
      List.fold_left
        (fun sigma def ->
          let d = def.Stmt.rec_defined in
          declare ~sigma d.Stmt.defined_head d.Stmt.defined_ty)
        sigma l
  | Stmt.Axiom (Stmt.Axiom_spec _ | Stmt.Axiom_std _)
  | Stmt.Goal _ -> sigma
  | Stmt.TyDef (_,l) ->
      List.fold_left
        (fun sigma tydef ->
          let sigma = declare ~sigma tydef.Stmt.ty_id tydef.Stmt.ty_type in
          ID.Map.fold
            (fun _ cstor sigma ->
              declare ~sigma cstor.Stmt.cstor_name cstor.Stmt.cstor_type
            ) tydef.Stmt.ty_cstors sigma
        ) sigma l
