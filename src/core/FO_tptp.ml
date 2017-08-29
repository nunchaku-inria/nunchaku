
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 TPTP representation} *)

type ty = Unitype
type var = ty Var.t

type term =
  | App of ID.t * term list
  | Var of var
  | True
  | False
  | Undefined_atom of term list (* ?__ args *)

type form =
  | And of form list
  | Or of form list
  | Not of form
  | Imply of form * form
  | Equiv of form * form
  | Atom of term
  | Eq of term * term
  | Neq of term * term
  | Forall of var * form
  | Exists of var * form

type role =
  | R_axiom
  | R_conjecture

type statement = {
  st_name: string;
  st_role: role;
  st_form: form;
}

type problem = {
  pb_statements: statement CCVector.ro_vector;
  pb_meta: ProblemMetadata.t;
}

(** {2 Basics} *)

let app id l = App (id,l)
let const id = app id []
let undefined_atom l = Undefined_atom l
let var v = Var v
let true_ = True
let false_ = False

let term_hash = function
  | App (f, _) -> ID.hash f
  | Var v -> Var.id v |> ID.hash
  | True
  | False
  | Undefined_atom _ -> 42

let rec term_equal a b = match a, b with
  | True, True
  | False, False -> true
  | Var v1, Var v2 -> Var.equal v1 v2
  | App (f1,l1), App (f2,l2) -> ID.equal f1 f2 && CCList.equal term_equal l1 l2
  | Undefined_atom l1, Undefined_atom l2 -> CCList.equal term_equal l1 l2
  | True, _ | False, _ | Var _, _ | App _, _ | Undefined_atom _, _ -> false

let is_var = function Var _ -> true | _ -> false

let and_ = function
  | [] -> Atom True
  | [x] -> x
  | l -> And l
let or_ = function
  | [] -> Atom False
  | [x] -> x
  | l -> Or l
let imply a b = Imply (a,b)
let equiv a b = Equiv (a,b)
let atom t = Atom t
let eq a b = Eq (a,b)
let neq a b = Neq (a,b)
let not_ = function
  | Neq (a,b) -> eq a b
  | Eq (a,b) -> neq a b
  | Not f -> f
  | f -> Not f
let forall v f = Forall (v,f)
let exists v f = Exists (v,f)
let forall_l = List.fold_right forall
let exists_l = List.fold_right exists

(* fresh, imaginative name *)
let mk_name_ =
  let n = ref 0 in
  fun () ->
    let x = Printf.sprintf "stmt_%d" !n in
    incr n;
    x

let axiom ?(name=mk_name_()) f =
  { st_name=name; st_role=R_axiom; st_form=f }

let conjecture ?(name=mk_name_()) f =
  { st_name=name; st_role=R_conjecture; st_form=f }

(** {2 IO} *)

module E = ID.Erase

let erase = E.create_state ()

let fpf = Format.fprintf
let pp_list ?(sep=", ") pp = Utils.pp_list ~sep pp

let pp_role_tptp out = function
  | R_axiom -> CCFormat.string out "axiom"
  | R_conjecture -> CCFormat.string out "conjecture"

let pp_var out v =
  (* build deterministic name for this variable *)
  let n = Var.name v |> CCString.capitalize_ascii in
  let n = Printf.sprintf "%s_%d" n (Var.id v |> ID.id) in
  CCFormat.string out n

(* map ID to a name, unambiguously *)
let name_of_id_ id =
  let encode _ = CCString.uncapitalize_ascii in
  E.to_name ~encode erase id

let rec pp_term_tptp out = function
  | Var v -> pp_var out v
  | App (id,[]) -> CCFormat.string out (name_of_id_ id)
  | App (id,l) ->
    fpf out "%s(@[<hv>%a@])" (name_of_id_ id) (pp_list pp_term_tptp) l
  | Undefined_atom [] -> fpf out "$undefined"
  | Undefined_atom l -> fpf out "$undefined(@[%a@])" (pp_list pp_term_tptp) l
  | True -> CCFormat.string out "$true"
  | False -> CCFormat.string out "$false"

let pp_form_tptp out f =
  let rec aux out = function
    | Atom t -> pp_term_tptp out t
    | And [] | Or [] -> assert false
    | And l -> fpf out "(@[<hv>%a@])" (pp_list ~sep:" & " aux) l
    | Or l -> fpf out "(@[<hv>%a@])" (pp_list ~sep:" | " aux) l
    | Not f -> fpf out "(@[~@ @[%a@]@])" aux f
    | Imply (a,b) ->
      fpf out "(@[@[%a@] =>@ @[%a@]@])" aux a aux b
    | Equiv (a,b) ->
      fpf out "(@[@[%a@] <=>@ @[%a@]@])" aux a aux b
    | Eq (a,b) ->
      fpf out "(@[@[%a@] =@ @[%a@]@])" pp_term_tptp a pp_term_tptp b
    | Neq (a,b) ->
      fpf out "(@[@[%a@] !=@ @[%a@]@])" pp_term_tptp a pp_term_tptp b
    | Forall (v,f) -> fpf out "(@[![%a]:@ @[%a@]@])" pp_var v aux f
    | Exists (v,f) -> fpf out "(@[?[%a]:@ @[%a@]@])" pp_var v aux f
  in
  aux out f

let pp_statement_tptp out st =
  fpf out "@[<2>fof(@[%s, %a,@ @[%a@]@]).@]"
    st.st_name pp_role_tptp st.st_role pp_form_tptp st.st_form

let pp_problem_tptp out pb =
  fpf out "@[<v>%a@]"
    (Utils.pp_seq ~sep:"" pp_statement_tptp)
    (CCVector.to_seq pb.pb_statements)
