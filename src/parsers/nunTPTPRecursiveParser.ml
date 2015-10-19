
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 TPTP Parser that removes "include" statements}

  This parser preprocesses TPTP problems to adapt them for Nunchaku:

  {ul
  {- recursively parse "include"-d files}
  {- declare TPTP primitives}
  {- declare symbols that are not normally declared}
  {- add "$i" to variables that have no type}
  }
*)

module A = NunUntypedAST
module P = NunTPTPParser
module Loc = NunLocation

let parse_ty = P.parse_ty
let parse_term = P.parse_term
let parse_statement = P.parse_statement

let section = NunUtils.Section.make "TPTPRecursiveParser"

(* where to find TPTP files *)
let tptp_dir () =
  try Some (Sys.getenv "TPTP") with Not_found -> None

let error_include_ ?loc f =
  NunParsingUtils.parse_error_ ?loc "include not found: `%s`" f

module StrTbl = CCHashtbl.Make(struct
  type t = string
  let equal = CCString.equal
  let hash = CCString.hash
end)

(* state for parsing *)
type state = {
  into: A.statement CCVector.vector; (* statements *)
  declared: unit StrTbl.t;
}

let create_state () = {
  into = CCVector.create ();
  declared = StrTbl.create 64;
}

let ty_term = A.var "$i"
let ty_prop = A.ty_prop (* proposition *)

let add_stmt ~state st = CCVector.push state.into st

let is_declared ~state s = StrTbl.mem state.declared s

type ctx =
  | Ctx_prop
  | Ctx_term
  | Ctx_ty

(* declare symbol with default type and given [arity] *)
let declare_sym ~state ~ctx s arity =
  let ty = match ctx with
    | Ctx_ty ->
        if arity<>0 then failwith "type must be declared";
        A.ty_type
    | Ctx_term ->
        let args = CCList.init arity (fun _ -> ty_term) in
        A.ty_arrow_list args ty_term
    | Ctx_prop ->
        let args = CCList.init arity (fun _ -> ty_term) in
        A.ty_arrow_list args ty_prop
  in
  NunUtils.debugf ~section 1 "declare `%s` with (default) type `%a`"
    s A.print_term ty;
  (* declare [s : ty] *)
  StrTbl.replace state.declared s ();
  CCVector.push state.into (A.decl s ty);
  ()

let enter_var_ ~state v f =
  (* enter the scope of [v] *)
  StrTbl.add state.declared v ();
  try
    f();
    StrTbl.remove state.declared v
  with e ->
    StrTbl.remove state.declared v;
    raise e

(* subterm of prop -> term *)
let prop2term = function
  | Ctx_prop -> Ctx_term
  | c -> c

(* add missing declarations of symbols and variables. Pushes
  declarations in [state] *)
let rec declare_missing ~ctx ~state t = match Loc.get t with
  | A.Wildcard
  | A.MetaVar _
  | A.Builtin _ -> ()
  | A.Var v
  | A.AtVar v ->
      if not (is_declared ~state v) then declare_sym ~ctx ~state v 0
  | A.App (f,l) ->
      begin match Loc.get f with
      | A.AtVar v
      | A.Var v ->
          if not (is_declared ~state v)
            then declare_sym ~state ~ctx v (List.length l);
          let ctx = prop2term ctx in
          List.iter (declare_missing ~ctx ~state) l
      | A.Builtin b ->
          begin match b with
          | A.Builtin.And
          | A.Builtin.Not
          | A.Builtin.Or
          | A.Builtin.Imply
          | A.Builtin.Equiv -> List.iter (declare_missing ~ctx:Ctx_prop ~state) l
          | A.Builtin.Eq -> List.iter (declare_missing ~ctx:Ctx_term ~state) l
          | A.Builtin.Prop
          | A.Builtin.Type
          | A.Builtin.True
          | A.Builtin.False -> ()
          end
      | _ ->
        let ctx = prop2term ctx in
        List.iter (declare_missing ~ctx ~state) l
      end;
  | A.Fun (v,t) ->
      enter_typed_var_ ~state v
      (fun () -> declare_missing ~ctx ~state t)
  | A.Let (v,t,u) ->
      enter_var_ ~state v
        (fun () ->
          declare_missing ~ctx ~state t; declare_missing ~ctx ~state u
        )
  | A.Ite (a,b,c) ->
      declare_missing ~state ~ctx:Ctx_prop a;
      declare_missing ~state ~ctx b;
      declare_missing ~state ~ctx c;
  | A.TyForall (v,t) ->
      enter_var_ ~state v
        (fun () -> declare_missing ~ctx:Ctx_ty ~state t)
  | A.Forall (v,t)
  | A.Exists (v,t) ->
      enter_typed_var_ ~state v
        (fun () -> declare_missing ~ctx:Ctx_prop ~state t)
  | A.TyArrow (a,b) ->
      declare_missing ~ctx:Ctx_ty ~state a;
      declare_missing ~ctx:Ctx_ty ~state b

(* "declare" a variable locally *)
and enter_typed_var_ ~state (v,ty_opt) f =
  (* declare missign type constructors *)
  CCOpt.iter (declare_missing ~ctx:Ctx_ty ~state) ty_opt;
  enter_var_ ~state v f

(* parse the lexbuf, and parse its includes recursively *)
let rec parse_rec_ ~state token lexbuf =
  let l = P.parse_statement_list token lexbuf in
  List.iter
    (fun st ->
      let loc = st.A.stmt_loc in
      match st.A.stmt_value with
      | A.Include (f, _which) ->
          (* TODO: handle partial includes *)
          (* include file *)
          if Sys.file_exists f then parse_file_ ~state token f
          else
            (* use the $TPTP env variable *)
            begin match tptp_dir () with
            | None -> error_include_ ?loc f
            | Some dir ->
                let f' = Filename.concat dir f in
                if not (Sys.file_exists f')
                  then error_include_ ?loc f;
                parse_file_ ~state token f'
            end
      | A.Axiom ax_l ->
          List.iter (declare_missing ~ctx:Ctx_prop ~state) ax_l;
          add_stmt ~state st
      | A.Decl (_,t) ->
          declare_missing ~ctx:Ctx_ty ~state t;
          add_stmt ~state st
      | A.Goal f ->
          declare_missing ~ctx:Ctx_prop ~state f;
          add_stmt ~state st
      | A.Spec _
      | A.Rec _
      | A.Data _
      | A.Codata _ -> add_stmt ~state st
    ) l

(* parse the given file *)
and parse_file_ ~state token f =
  CCIO.with_in f
    (fun ic ->
      let lexbuf = Lexing.from_channel ic in
      Loc.set_file lexbuf f;
      parse_rec_ ~state token lexbuf
    )

let parse_statement_list token lexbuf =
  let state = create_state() in
  parse_rec_ ~state token lexbuf;
  (* the prelude of TPTP: defined types *)
  let l = CCVector.to_list state.into in
  List.append A.TPTP.prelude l


