(* This file is free software, part of nunchaku. See file "license" for more details. *)

module ID = NunID
module Statement = NunStatement

type id = ID.t
type 'a printer = Format.formatter -> 'a -> unit

type ('t, 'ty) def =
  | Fun of ('t, 'ty) Statement.mutual_cases list
      (** ID is a defined fun/predicate. Can be defined in several places *)

  | Data of [`Codata | `Data] * 'ty Statement.mutual_types * 'ty Statement.tydef
      (** ID is a (co)data *)

  | Cstor of 'ty Statement.tydef * 'ty Statement.ty_constructor
      (** ID is a constructor (of the given type) *)

  | NoDef
      (** Undefined symbol *)

(** All information on a given symbol *)
type ('t, 'ty) info = {
  ty: 'ty; (** type of symbol *)
  def: ('t, 'ty) def;
}

(** Maps ID to their type and definitions *)
type ('t, 'ty) t = {
  infos: ('t, 'ty) info NunID.Tbl.t;
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

let create() = {infos=ID.Tbl.create 64}

let check_not_defined_ t ~id ~fail_msg =
  if ID.Tbl.mem t.infos id then errorf_ id fail_msg

let declare ~env:t ~id ~ty =
  check_not_defined_ t ~id ~fail_msg:"already declared";
  let info = {ty; def=NoDef} in
  ID.Tbl.replace t.infos id info

let def_funs ~env:t cases =
  List.iter
    (fun c ->
      let id = c.Statement.case_head in
      try
        let info = ID.Tbl.find t.infos id in
        let l = match info.def with
          | Data _ -> errorf_ id "defined as both function and (co)data"
          | Cstor _ -> errorf_ id "defined as both function and constructor"
          | Fun l -> l
          | NoDef -> [] (* first def of id *)
        in
        let def = Fun (cases :: l) in
        ID.Tbl.replace t.infos id {info with def; }
      with Not_found ->
        errorf_ id "defined function, but not declared previously"
    ) cases

let def_data ~env:t ~kind tys =
  List.iter
    (fun tydef ->
      (* define type *)
      let id = tydef.Statement.ty_id in
      check_not_defined_ t ~id ~fail_msg:"is (co)data, but already defined";
      let info = {
        ty=tydef.Statement.ty_type;
        def=Data (kind, tys, tydef);
      } in
      ID.Tbl.replace t.infos id info;
      (* define constructors *)
      List.iter
        (fun cstor ->
          let id = cstor.Statement.cstor_name in
          check_not_defined_ t ~id ~fail_msg:"is constructor, but already defined";
          let info = {
            ty=cstor.Statement.cstor_type;
            def=Cstor (tydef, cstor);
          } in
          ID.Tbl.replace t.infos id info;
        ) tydef.Statement.ty_cstors
    ) tys

let find_exn ~env:t ~id = ID.Tbl.find t.infos id

let find ~env:t ~id =
  try Some (find_exn ~env:t ~id)
  with Not_found -> None

let mem ~env ~id = ID.Tbl.mem env.infos id

let find_ty ~env ~id = (find_exn ~env ~id).ty
