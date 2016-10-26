(* This file is free software, part of nunchaku. See file "license" for more details. *)

module TI = TermInner
module Stmt = Statement
module Loc = Location

type id = ID.t
type loc = Loc.t
type 'a printer = Format.formatter -> 'a -> unit

type (+'t, +'ty) def =
  | Fun_def of
      ('t, 'ty) Statement.rec_defs *
      ('t, 'ty) Statement.rec_def *
      loc option
      (** ID is a defined fun/predicate. *)

  | Fun_spec of
      ('t, 'ty) Statement.spec_defs * loc option

  | Data of
      [`Codata | `Data] *
      'ty Statement.mutual_types *
      'ty Statement.tydef
      (** ID is a (co)data *)

  | Cstor of
      [`Codata | `Data] *
      'ty Statement.mutual_types *
      'ty Statement.tydef *
      'ty Statement.ty_constructor
      (** ID is a constructor (of the given type) *)

  | Pred of
      [`Wf | `Not_wf] *
      [`Pred | `Copred] *
      ('t, 'ty) Statement.pred_def *
      ('t, 'ty) Statement.pred_def list *
      loc option

  | Copy_ty of ('t, 'ty) Statement.copy
    (** ID is the copy type *)

  | Copy_abstract of ('t, 'ty) Statement.copy
    (** ID is the abstraction function *)

  | Copy_concrete of ('t, 'ty) Statement.copy
    (** ID is the concretization function *)

  | NoDef
    (** Undefined symbol *)

(** All information on a given symbol *)
type (+'t, +'ty) info = {
  ty: 'ty; (** type of symbol *)
  decl_attrs: Statement.decl_attr list;
  loc: loc option;
  def: ('t, 'ty) def;
}

(** Maps ID to their type and definitions *)
type ('t, 'ty) t = {
  infos: ('t, 'ty) info ID.PerTbl.t;
}

exception InvalidDef of id * string
exception UndefinedID of ID.t

let pp_invalid_def_ out = function
  | InvalidDef (id, msg) ->
      Format.fprintf out "@[<2>invalid definition for `%a`:@ %s@]" ID.print id msg
  | _ -> assert false

let () = Printexc.register_printer
  (function
    | InvalidDef _ as e ->
        Some (Utils.err_sprintf "env: %a" pp_invalid_def_ e)
    | UndefinedID id ->
        Some (Utils.err_sprintf "env: undefined ID `%a`" ID.print id)
    | _ -> None
  )

let errorf_ id msg =
  Utils.exn_ksprintf msg ~f:(fun msg -> raise (InvalidDef(id,msg)))

let loc t = t.loc
let def t = t.def
let ty t = t.ty

let is_fun i = match i.def with Fun_spec _ | Fun_def _ -> true | _ -> false
let is_rec i = match i.def with Fun_def _ -> true | _ -> false
let is_data i = match i.def with Data _ -> true | _ -> false
let is_cstor i = match i.def with Cstor _ -> true | _ -> false
let is_not_def i = match i.def with NoDef -> true | _ -> false

let is_incomplete i =
  List.exists (function Stmt.Attr_incomplete -> true | _ -> false) i.decl_attrs
let is_abstract i =
  List.exists (function Stmt.Attr_abstract -> true | _ -> false) i.decl_attrs

let create ?(size=64) () = {infos=ID.PerTbl.create size}

let check_not_defined_ t ~id ~fail_msg =
  if ID.PerTbl.mem t.infos id then errorf_ id fail_msg

let declare ?loc ~attrs ~env:t id ty =
  check_not_defined_ t ~id ~fail_msg:"already declared";
  let info = {loc; decl_attrs=attrs; ty; def=NoDef} in
  {infos=ID.PerTbl.replace t.infos id info}

let rec_funs ?loc ~env:t defs =
  List.fold_left
    (fun t def ->
      let id = def.Stmt.rec_defined.Stmt.defined_head in
      if ID.PerTbl.mem t.infos id
        then errorf_ id "already declared or defined";
      let info = {
        loc;
        ty=def.Stmt.rec_defined.Stmt.defined_ty;
        decl_attrs=[];
        def=Fun_def (defs, def, loc);
      } in
      {infos=ID.PerTbl.replace t.infos id info}
    ) t defs

let declare_rec_funs ?loc ~env defs =
  List.fold_left
    (fun env def ->
      let d = def.Stmt.rec_defined in
      let id = d.Stmt.defined_head in
      declare ~attrs:[] ?loc ~env id d.Stmt.defined_ty)
    env defs

let find_exn ~env:t id =
  try ID.PerTbl.find t.infos id
  with Not_found -> raise (UndefinedID id)

let find ~env:t id =
  try Some (ID.PerTbl.find t.infos id)
  with Not_found -> None

let spec_funs ?loc ~env:t spec =
  List.fold_left
    (fun t defined ->
      let id = defined.Stmt.defined_head in
      if ID.PerTbl.mem t.infos id
        then errorf_ id "already declared or defined";
      let info = {
        loc;
        ty=defined.Stmt.defined_ty;
        decl_attrs=[];
        def=Fun_spec(spec, loc);
      } in
      {infos=ID.PerTbl.replace t.infos id info; }
    )
    t spec.Stmt.spec_defined

let def_data ?loc ~env:t ~kind tys =
  List.fold_left
    (fun t tydef ->
      (* define type *)
      let id = tydef.Stmt.ty_id in
      check_not_defined_ t ~id ~fail_msg:"is (co)data, but already defined";
      let info = {
        loc;
        ty=tydef.Stmt.ty_type;
        decl_attrs=[];
        def=Data (kind, tys, tydef);
      } in
      let t = {infos=ID.PerTbl.replace t.infos id info} in
      (* define constructors *)
      ID.Map.fold
        (fun _ cstor t ->
          let id = cstor.Stmt.cstor_name in
          check_not_defined_ t ~id ~fail_msg:"is constructor, but already defined";
          let info = {
            loc;
            ty=cstor.Stmt.cstor_type;
            decl_attrs=[];
            def=Cstor (kind,tys,tydef, cstor);
          } in
          {infos=ID.PerTbl.replace t.infos id info}
        ) tydef.Stmt.ty_cstors t
    ) t tys

let def_pred ?loc ~env ~wf ~kind def l =
  let id = def.Stmt.pred_defined.Stmt.defined_head in
  check_not_defined_ env ~id
    ~fail_msg:"is (co)inductive pred, but already defined";
  let info = {
    loc;
    ty=def.Stmt.pred_defined.Stmt.defined_ty;
    decl_attrs=[];
    def=Pred(wf,kind,def,l,loc);
  } in
  {infos=ID.PerTbl.replace env.infos id info}


let def_preds ?loc ~env ~wf ~kind l =
  List.fold_left
    (fun env def ->
      def_pred ?loc ~env ~wf ~kind def l)
    env l

let add_copy ?loc ~env c =
  let infos = env.infos in
  let infos =
    ID.PerTbl.replace infos c.Stmt.copy_id
      {loc; decl_attrs=[];
       ty=c.Stmt.copy_ty; def=Copy_ty c; } in
  let infos =
    ID.PerTbl.replace infos c.Stmt.copy_abstract
      {loc; decl_attrs=[];
       ty=c.Stmt.copy_abstract_ty; def=Copy_abstract c; } in
  let infos =
    ID.PerTbl.replace infos c.Stmt.copy_concrete
      {loc; decl_attrs=[];
       ty=c.Stmt.copy_concrete_ty; def=Copy_concrete c; } in
  {infos; }

let add_statement ~env st =
  let loc = Stmt.loc st in
  match Stmt.view st with
  | Stmt.Decl (id,ty,attrs) ->
      declare ?loc ~attrs ~env id ty
  | Stmt.TyDef (kind,l) ->
      def_data ?loc ~env ~kind l
  | Stmt.Goal _ -> env
  | Stmt.Axiom (Stmt.Axiom_std _) -> env
  | Stmt.Axiom (Stmt.Axiom_spec l) ->
      spec_funs ?loc ~env l
  | Stmt.Axiom (Stmt.Axiom_rec l) ->
      rec_funs ?loc ~env l
  | Stmt.Copy c ->
      add_copy ?loc ~env c
  | Stmt.Pred (wf, kind, preds) ->
      def_preds ?loc ~env ~wf ~kind preds

let add_statement_l ~env l =
  List.fold_left (fun env st -> add_statement ~env st) env l

let mem ~env ~id = ID.PerTbl.mem env.infos id

let find_ty_exn ~env id = (find_exn ~env id).ty

let find_ty ~env id = CCOpt.map (fun x -> x.ty) (find ~env id)

module Util(T : TermInner.S) = struct
  type term = T.t
  type ty = T.t

  module UT = TI.Util(T)

  let ty ~env t = UT.ty ~sigma:(find_ty ~env) t

  let ty_exn ~env t = UT.ty_exn ~sigma:(find_ty ~env) t

  exception No_head of ty

  let info_of_ty_exn ~env ty =
    try
      let id = UT.head_sym ty in
      find_exn ~env id
    with Not_found -> raise (No_head ty)

  let info_of_ty ~env ty =
    try Result.Ok (info_of_ty_exn ~env ty)
    with No_head _ -> Result.Error "type has no head"
end

module Print(Pt : TermInner.PRINT)(Pty : TermInner.PRINT) = struct
  let fpf = Format.fprintf

  let print_def out = function
    | Fun_def _ -> CCFormat.string out "<rec>"
    | Fun_spec _ -> CCFormat.string out "<spec>"
    | Data _ -> CCFormat.string out "<data>"
    | Cstor (_,_,_,{ Stmt.cstor_type; _ }) ->
        fpf out "<cstor : `%a`>" Pty.print cstor_type
    | Pred _ -> CCFormat.string out "<pred>"
    | Copy_ty { Stmt.copy_of; _ } -> fpf out "<copy of `%a`>" Pty.print copy_of
    | Copy_abstract { Stmt.copy_id; _ } ->
        fpf out "<copy abstract of `%a`>" ID.print copy_id
    | Copy_concrete { Stmt.copy_id; _ } ->
        fpf out "<copy concrete of `%a`>" ID.print copy_id
    | NoDef -> CCFormat.string out "<no def>"

  let print_info out i =
    fpf out "@[<2>@,: `@[%a@]`@ := %a%a@]" Pty.print i.ty
      print_def i.def Stmt.print_attrs i.decl_attrs

  let print out e =
    let print_pair out (id,info) =
      fpf out "@[%a %a@]" ID.print id print_info info
    in
    fpf out "@[<v>@[<v2>env {@,@[<v>%a@]@]@,}@]"
      (CCFormat.seq ~start:"" ~stop:"" print_pair) (ID.PerTbl.to_seq e.infos)
end
