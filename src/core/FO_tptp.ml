
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 TPTP representation} *)

type ty = Unitype
type var = ty Var.t

type term =
  | App of ID.t * term list
  | Var of var
  | True
  | False
  | Undefined of term

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
let undefined t = Undefined t
let var v = Var v
let true_ = True
let false_ = False

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
let pp_list ?(sep=", ") pp = CCFormat.list ~start:"" ~stop:"" ~sep pp

let print_role_tptp out = function
  | R_axiom -> CCFormat.string out "axiom"
  | R_conjecture -> CCFormat.string out "conjecture"

let pp_var out v =
  (* build deterministic name for this variable *)
  let n = Var.name v |> String.capitalize in
  let n = Printf.sprintf "%s_%d" n (Var.id v |> ID.id) in
  CCFormat.string out n

(* map ID to a name, unambiguously *)
let name_of_id_ id =
  let encode _ = String.uncapitalize in
  E.to_name ~encode erase id

let rec print_term_tptp out = function
  | Var v -> pp_var out v
  | App (id,[]) -> CCFormat.string out (name_of_id_ id)
  | App (id,l) ->
    fpf out "%s(@[<hv>%a@])" (name_of_id_ id) (pp_list print_term_tptp) l
  | Undefined t -> fpf out "$undefined(@[%a@])" print_term_tptp t
  | True -> CCFormat.string out "$true"
  | False -> CCFormat.string out "$false"

(* precedence. Order matters, as it defines priorities *)
type prec =
  | P_not
  | P_bind
  | P_and
  | P_or

let right_assoc_ = function
  | P_and
  | P_or -> false
  | P_not
  | P_bind -> true

(* put () if needed *)
let wrap p1 p2 out fmt =
  if p1>p2 || (p1 = p2 && (not (right_assoc_ p1)))
  then (
    CCFormat.string out "(";
    Format.kfprintf (fun _ -> CCFormat.string out ")") out fmt
  )
  else Format.kfprintf (fun _ -> ()) out fmt

let print_form_tptp out f =
  let rec aux p out = function
    | Atom t -> print_term_tptp out t
    | And [] | Or [] -> assert false
    | And l -> wrap P_and p out "@[<hv>%a@]" (pp_list ~sep:" & " (aux P_and)) l
    | Or l -> wrap P_or p out "@[<hv>%a@]" (pp_list ~sep:" | " (aux P_or)) l
    | Not f -> wrap P_not p out "@[~@ @[%a@]@]" (aux P_not) f
    | Imply (a,b) ->
      wrap P_or p out "@[@[%a@] =>@ @[%a@]@]" (aux P_or) a (aux P_or) b
    | Equiv (a,b) ->
      wrap P_or p out "@[@[%a@] <=>@ @[%a@]@]" (aux P_or) a (aux P_or) b
    | Eq (a,b) ->
      fpf out "@[@[%a@] =@ @[%a@]@]" print_term_tptp a print_term_tptp b
    | Neq (a,b) ->
      fpf out "@[@[%a@] !=@ @[%a@]@]" print_term_tptp a print_term_tptp b
    | Forall (v,f) -> wrap P_bind p out "@[![%a]:@ @[%a@]@]" pp_var v (aux P_bind) f
    | Exists (v,f) -> wrap P_bind p out "@[?[%a]:@ @[%a@]@]" pp_var v (aux P_bind) f
  in
  aux P_bind out f

let print_statement_tptp out st =
  fpf out "@[<2>fof(@[%s, %a,@ @[%a@]@]).@]"
    st.st_name print_role_tptp st.st_role print_form_tptp st.st_form

let print_problem_tptp out pb =
  fpf out "@[<v>%a@]"
    (CCVector.print ~start:"" ~stop:"" ~sep:"" print_statement_tptp) pb.pb_statements
