(* This file is free software, part of nunchaku. See file "license" for more details. *)

module ID = ID
module Stmt = Statement

type id = ID.t

type 'ty t = 'ty ID.Map.t

let empty = ID.Map.empty

let mem ~sigma id = ID.Map.mem id sigma
let find_exn ~sigma id = ID.Map.find id sigma
let find ~sigma id =
  try Some (find_exn ~sigma id)
  with Not_found -> None

let declare ~sigma id ty = ID.Map.add id ty sigma

let add_list ~sigma l =
  List.fold_left (fun sigma (id,ty) -> declare ~sigma id ty) sigma l

let of_list l = add_list ~sigma:empty l

let add_pred (type inv) ~sigma (pred:(_,_,inv) Stmt.pred_def) =
  let d = pred.Stmt.pred_defined in
  declare ~sigma d.Stmt.defined_head d.Stmt.defined_ty

let add_preds ~sigma preds =
  List.fold_left (fun sigma d -> add_pred ~sigma d) sigma preds

let add_statement ~sigma st = match Stmt.view st with
  | Stmt.Decl (id,_,ty,_) -> declare ~sigma id ty
  | Stmt.Axiom (Stmt.Axiom_rec l) ->
      List.fold_left
        (fun sigma def ->
          let d = def.Stmt.rec_defined in
          declare ~sigma d.Stmt.defined_head d.Stmt.defined_ty)
        sigma l
  | Stmt.Axiom (Stmt.Axiom_spec s) ->
      List.fold_left
        (fun sigma def ->
          declare ~sigma def.Stmt.defined_head def.Stmt.defined_ty)
        sigma s.Stmt.spec_defined
  | Stmt.Axiom (Stmt.Axiom_std _)
  | Stmt.Goal _ -> sigma
  | Stmt.Pred (_, _, preds) -> add_preds ~sigma preds
  | Stmt.Copy c ->
      let sigma = declare ~sigma c.Stmt.copy_id c.Stmt.copy_ty in
      let sigma = declare ~sigma c.Stmt.copy_abstract c.Stmt.copy_abstract_ty in
      let sigma = declare ~sigma c.Stmt.copy_concrete c.Stmt.copy_concrete_ty in
      sigma
  | Stmt.TyDef (_,l) ->
      List.fold_left
        (fun sigma tydef ->
          let sigma = declare ~sigma tydef.Stmt.ty_id tydef.Stmt.ty_type in
          ID.Map.fold
            (fun _ cstor sigma ->
              declare ~sigma cstor.Stmt.cstor_name cstor.Stmt.cstor_type)
            tydef.Stmt.ty_cstors sigma)
        sigma l
