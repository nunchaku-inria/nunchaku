(* This file is free software, part of nunchaku. See file "license" for more details. *)

module ID = NunID
module Stmt = NunStatement
module Loc = NunLocation

type id = ID.t
type loc = Loc.t
type 'a printer = Format.formatter -> 'a -> unit


type ('t, 'ty, 'inv) fun_def =
  | Rec of
      ('t, 'ty, 'inv) NunStatement.rec_defs *
      ('t, 'ty, 'inv) NunStatement.rec_def *
      loc option
  | Spec of
      ('t, 'ty) NunStatement.spec_defs *
      loc option

type ('t, 'ty, 'inv) def =
  | Fun of ('t, 'ty, 'inv) fun_def list
      (** ID is a defined fun/predicate. Can be defined in several places *)

  | Data of [`Codata | `Data] * 'ty NunStatement.mutual_types * 'ty NunStatement.tydef
      (** ID is a (co)data *)

  | Cstor of
      [`Codata | `Data] *
      'ty NunStatement.mutual_types *
      'ty NunStatement.tydef *
      'ty NunStatement.ty_constructor
      (** ID is a constructor (of the given type) *)

  | NoDef
      (** Undefined symbol *)

(** All information on a given symbol *)
type ('t, 'ty, 'inv) info = {
  ty: 'ty; (** type of symbol *)
  decl_kind: NunStatement.decl;
  loc: loc option;
  def: ('t, 'ty, 'inv) def;
}

(** Maps ID to their type and definitions *)
type ('t, 'ty, 'inv) t = {
  infos: ('t, 'ty, 'inv) info NunID.PerTbl.t;
}

exception InvalidDef of id * string

let pp_invalid_def_ out = function
  | InvalidDef (id, msg) ->
      Format.fprintf out "invalid definition for ID %a: %s" ID.print_name id msg
  | _ -> assert false

let () = Printexc.register_printer
  (function
      | InvalidDef _ as e -> Some (CCFormat.to_string pp_invalid_def_ e)
      | _ -> None
  )

let errorf_ id msg =
  NunUtils.exn_ksprintf msg ~f:(fun msg -> raise (InvalidDef(id,msg)))

let loc t = t.loc
let def t = t.def
let ty t = t.ty
let decl_kind t = t.decl_kind

let create() = {infos=ID.PerTbl.create 64}

let check_not_defined_ t ~id ~fail_msg =
  if ID.PerTbl.mem t.infos id then errorf_ id fail_msg

let declare ?loc ~kind ~env:t id ty =
  check_not_defined_ t ~id ~fail_msg:"already declared";
  let info = {loc; decl_kind=kind; ty; def=NoDef} in
  {infos=ID.PerTbl.replace t.infos id info}

let rec_funs ?loc ~env:t defs =
  List.fold_left
    (fun t def ->
      let id = def.Stmt.rec_defined.Stmt.defined_head in
      try
        let info = ID.PerTbl.find t.infos id in
        let l = match info.def with
          | Data _ -> errorf_ id "defined as both function and (co)data"
          | Cstor _ -> errorf_ id "defined as both function and constructor"
          | Fun l -> l
          | NoDef -> [] (* first def of id *)
        in
        let def = Fun ((Rec(defs, def, loc)) :: l) in
        {infos=ID.PerTbl.replace t.infos id {info with def; }}
      with Not_found ->
        errorf_ id "defined function, but not declared previously"
    ) t defs

let spec_funs ?loc ~env:t spec =
  List.fold_left
    (fun t defined ->
      let id = defined.Stmt.defined_head in
      try
        let info = ID.PerTbl.find t.infos id in
        let l = match info.def with
          | Data _ -> errorf_ id "defined as both function and (co)data"
          | Cstor _ -> errorf_ id "defined as both function and constructor"
          | Fun l -> l
          | NoDef -> [] (* first def of id *)
        in
        let def = Fun ((Spec(spec, loc)) :: l) in
        {infos=ID.PerTbl.replace t.infos id {info with def; }}
      with Not_found ->
        errorf_ id "defined function, but not declared previously"
    ) t spec.Stmt.spec_defined

let def_data ?loc ~env:t ~kind tys =
  List.fold_left
    (fun t tydef ->
      (* define type *)
      let id = tydef.Stmt.ty_id in
      check_not_defined_ t ~id ~fail_msg:"is (co)data, but already defined";
      let info = {
        loc;
        decl_kind=Stmt.Decl_type;
        ty=tydef.Stmt.ty_type;
        def=Data (kind, tys, tydef);
      } in
      let t = {infos=ID.PerTbl.replace t.infos id info} in
      (* define constructors *)
      List.fold_left
        (fun t cstor ->
          let id = cstor.Stmt.cstor_name in
          check_not_defined_ t ~id ~fail_msg:"is constructor, but already defined";
          let info = {
            loc;
            decl_kind=Stmt.Decl_fun;
            ty=cstor.Stmt.cstor_type;
            def=Cstor (kind,tys,tydef, cstor);
          } in
          {infos=ID.PerTbl.replace t.infos id info}
        ) t tydef.Stmt.ty_cstors
    ) t tys

let find_exn ~env:t ~id = ID.PerTbl.find t.infos id

let find ~env:t ~id =
  try Some (find_exn ~env:t ~id)
  with Not_found -> None

let mem ~env ~id = ID.PerTbl.mem env.infos id

let find_ty ~env ~id = (find_exn ~env ~id).ty
