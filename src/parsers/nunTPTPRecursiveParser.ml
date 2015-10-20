
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
let ty_type = A.ty_type

let add_stmt ~state st = CCVector.push state.into st

let is_declared ~state s = StrTbl.mem state.declared s

type ctx =
  | Ctx_prop
  | Ctx_term
  | Ctx_ty

(* symbol explicitely declared *)
let declare_sym ~state s =
  StrTbl.replace state.declared s ()

(* declare symbol with default type and given [arity] *)
let declare_sym_default ~state ~ctx s arity =
  let ty = match ctx with
    | Ctx_ty ->
        let args = CCList.init arity (fun _ -> ty_type) in
        A.ty_arrow_list args ty_type
    | Ctx_term ->
        let args = CCList.init arity (fun _ -> ty_term) in
        A.ty_arrow_list args ty_term
    | Ctx_prop ->
        let args = CCList.init arity (fun _ -> ty_term) in
        A.ty_arrow_list args ty_prop
  in
  NunUtils.debugf ~section 1 "declare `%s` with (default) type `%a`"
    (fun k-> k s A.print_term ty);
  (* declare [s : ty] *)
  StrTbl.replace state.declared s ();
  CCVector.push state.into (A.decl s ty);
  ()

let enter_var_ ~state v f =
  (* enter the scope of [v] *)
  StrTbl.add state.declared v ();
  try
    let x = f() in
    StrTbl.remove state.declared v;
    x
  with e ->
    StrTbl.remove state.declared v;
    raise e

(* close formula universally *)
let close_forall t =
  let fvars = StrTbl.create 16 in
  let bvars = StrTbl.create 16 in
  (* recursively compute set of free vars *)
  let rec compute_fvars t = match Loc.get t with
    | A.Var v ->
        if not (StrTbl.mem bvars v) then StrTbl.replace fvars v ()
    | A.Wildcard
    | A.Builtin _
    | A.AtVar _
    | A.MetaVar _ -> ()
    | A.App (f,l) -> compute_fvars f; List.iter compute_fvars l
    | A.Let (v,t,u) -> compute_fvars t; enter_bvar v (fun () -> compute_fvars u)
    | A.Ite (a,b,c) -> compute_fvars a; compute_fvars b; compute_fvars c
    | A.Forall (v,t)
    | A.Exists (v,t)
    | A.Fun (v,t) -> enter_ty_bvar v (fun () -> compute_fvars t)
    | A.TyArrow (a,b) -> compute_fvars a; compute_fvars b
    | A.TyForall (v,t) -> enter_bvar v (fun () -> compute_fvars t)
  and enter_bvar v f =
    StrTbl.add bvars v (); let x = f () in StrTbl.remove bvars v; x
  and enter_ty_bvar (v, tyopt) f =
    CCOpt.iter compute_fvars tyopt;
    enter_bvar v f
  in
  compute_fvars t;
  (* typed free variables *)
  let fvars = StrTbl.to_list fvars
    |> List.map (fun (v,_) -> v, None) in
  A.forall_list fvars t

(* subterm of prop -> term *)
let prop2term = function
  | Ctx_prop -> Ctx_term
  | c -> c

(* add missing declarations of symbols and variables. Pushes
  declarations in [state], and return a new term with all variables
  annotated with a type *)
let rec declare_missing ~ctx ~state t =
  match Loc.get t with
  | A.Wildcard
  | A.MetaVar _
  | A.Builtin _ -> t
  | A.Var v
  | A.AtVar v ->
      if not (is_declared ~state v) then declare_sym_default ~ctx ~state v 0;
      t
  | A.App (f,l) ->
      begin match Loc.get f with
      | A.AtVar v
      | A.Var v ->
          if not (is_declared ~state v)
            then declare_sym_default ~state ~ctx v (List.length l);
          let ctx = prop2term ctx in
          let l = List.map (declare_missing ~ctx ~state) l in
          A.app f l
      | A.Builtin b ->
          begin match b with
          | A.Builtin.And
          | A.Builtin.Not
          | A.Builtin.Or
          | A.Builtin.Imply
          | A.Builtin.Equiv ->
              let l = List.map (declare_missing ~ctx:Ctx_prop ~state) l in
              A.app f l
          | A.Builtin.Eq ->
              A.app f (List.map (declare_missing ~ctx:Ctx_term ~state) l)
          | A.Builtin.Prop
          | A.Builtin.Type
          | A.Builtin.True
          | A.Builtin.False -> t
          end
      | _ ->
        let ctx = prop2term ctx in
        A.app f (List.map (declare_missing ~ctx ~state) l)
      end;
  | A.Fun (v,t) ->
      enter_typed_var_ ~state v
        (fun v -> A.fun_ v (declare_missing ~ctx ~state t))
  | A.Let (v,t,u) ->
      let t = declare_missing ~ctx ~state t in
      enter_var_ ~state v
        (fun () -> A.let_ v t (declare_missing ~ctx ~state u))
  | A.Ite (a,b,c) ->
      A.ite
        (declare_missing ~state ~ctx:Ctx_prop a)
        (declare_missing ~state ~ctx b)
        (declare_missing ~state ~ctx c)
  | A.TyForall (v,t) ->
      enter_var_ ~state v
        (fun () -> A.ty_forall v (declare_missing ~ctx:Ctx_ty ~state t))
  | A.Forall (v,t) ->
      enter_typed_var_ ~state v
        (fun v -> A.forall v (declare_missing ~ctx:Ctx_prop ~state t))
  | A.Exists (v,t) ->
      enter_typed_var_ ~state v
        (fun v -> A.exists v (declare_missing ~ctx:Ctx_prop ~state t))
  | A.TyArrow (a,b) ->
      A.ty_arrow
        (declare_missing ~ctx:Ctx_ty ~state a)
        (declare_missing ~ctx:Ctx_ty ~state b)

(* "declare" a variable locally *)
and enter_typed_var_ ~state (v,ty_opt) f =
  (* declare missign type constructors *)
  let ty = match ty_opt with
    | None -> Some ty_term
    | Some ty -> Some (declare_missing ~ctx:Ctx_ty ~state ty)
  in
  enter_var_ ~state v (fun () -> f (v,ty))

let process_form ~state t =
  let t = declare_missing ~ctx:Ctx_prop ~state t in
  close_forall t

(* parse the lexbuf, and parse its includes recursively *)
let rec parse_rec_ ~basedir ~state token lexbuf =
  let l = P.parse_statement_list token lexbuf in
  (* try the list of files, parse the first existing one *)
  let rec try_files ?loc ~state token f l = match l with
    | [] -> error_include_ ?loc f
    | f' :: _ when Sys.file_exists f' -> parse_file_ ~state token f'
    | _ :: l' -> try_files ?loc ~state token f l'
  in
  List.iter
    (fun st ->
      let loc = st.A.stmt_loc in
      match st.A.stmt_value with
      | A.Include (f, _which) ->
          (* TODO: handle partial includes *)
          (* include file *)
          let files =
            f
            :: (Filename.concat basedir (Filename.basename f))
            :: (match tptp_dir () with
                | None -> []
                | Some dir -> [Filename.concat dir f] (* $TPTP/f *)
               )
          in
          try_files ?loc ~state token f files
      | A.Axiom ax_l ->
          let l = List.map (process_form ~state) ax_l in
          add_stmt ~state {st with A.stmt_value=A.Axiom l}
      | A.Decl (v,t) ->
          declare_sym ~state v; (* explicitely declared *)
          let t = declare_missing ~ctx:Ctx_ty ~state t in
          add_stmt ~state {st with A.stmt_value=A.Decl (v,t)}
      | A.Goal f ->
          let f = process_form ~state f in
          add_stmt ~state {st with A.stmt_value=A.Goal f}
      | A.Spec _
      | A.Rec _
      | A.Data _
      | A.Codata _ -> add_stmt ~state st (* NOTE: should not happen *)
    ) l

(* parse the given file *)
and parse_file_ ~state token f =
  CCIO.with_in f
    (fun ic ->
      let lexbuf = Lexing.from_channel ic in
      Loc.set_file lexbuf f;
      let basedir = Filename.dirname f in
      parse_rec_ ~basedir ~state token lexbuf
    )

let parse_statement_list token lexbuf =
  let state = create_state() in
  let basedir = Filename.dirname (Loc.get_file lexbuf) in
  parse_rec_ ~basedir ~state token lexbuf;
  (* the prelude of TPTP: defined types *)
  let l = CCVector.to_list state.into in
  List.append A.TPTP.prelude l


