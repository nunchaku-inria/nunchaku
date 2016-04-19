
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Relational FO Logic} *)

(** {2 Types} *)

type tuple = ID.Set.t

type unop =
  | Flip (** flip p x y <=> p y x *)
  | Trans (** trans p == transitive closure *)

type binop =
  | Union
  | Inter
  | Diff
  | Join (** join (x,y) (y,z) == (x,z) *)
  | Concat (** concat (x1,y1) (x2,y2) == (x1,y1,x2,y2) *)

type mult =
  | M_no
  | M_one
  | M_some

type expr =
  | Const of ID.t
  | Var of expr Var.t
  | Unop of unop * expr
  | Binop of binop * expr * expr
  | Comprehension of expr Var.t * form

and form =
  | In of expr * expr
  | Mult of mult * expr
  | Not of form
  | And of form * form
  | Or of form * form
  | Forall of expr Var.t * form
  | Exists of expr Var.t * form

type decl = {
  decl_id: ID.t;
  decl_arity: int;
  decl_low: tuple; (* lower bound *)
  decl_high: tuple; (* higher bound *)
}

type problem = {
  pb_univ: ID.Set.t;
  pb_decls: decl CCVector.ro_vector;
  pb_goal: form;
}

(** {2 Helpers} *)

let unop o a = Unop (o,a)
let binop o a b = Binop (o,a,b)
let mult m a = Mult (m,a)

let flip a = unop Flip a
let trans a = unop Trans a
let const id = Const id
let var v = Var v
let union = binop Union
let inter = binop Inter
let diff = binop Diff
let join = binop Join
let concat = binop Concat
let comprehension v f = Comprehension (v,f)

let in_ a b = In (a,b)
let no = mult M_no
let one = mult M_one
let some = mult M_some
let not_ a = Not a
let and_ a b = And (a,b)
let and_l = function
  | [] -> invalid_arg "and_l"
  | a :: tl -> List.fold_left and_ a tl
let or_ a b = Or(a,b)
let or_l = function
  | [] -> invalid_arg "or_l"
  | a :: tl -> List.fold_left or_ a tl
let for_all v f = Forall (v,f)
let exists v f = Exists (v,f)

(** {2 IO} *)

let fpf = Format.fprintf

let print_tuple out s =
  fpf out "{@[%a@]}" (ID.Set.print ~start:"" ~stop:"" ~sep:", " ID.print) s

(* precedence level *)
type prec =
  | P_unop
  | P_binop
  | P_f_not
  | P_f_and
  | P_f_or
  | P_f_quant
  | P_top

let compare_prec : prec CCOrd.t = Pervasives.compare

(* if [p1 < p2], then print [msg] surrounded with parenthesis, else print [msg] *)
let wrapf_ p1 p2 out msg =
  let wrap = compare_prec p1 p2 < 0 in
  if wrap then Format.pp_print_char out '(';
  Format.kfprintf
    (fun out -> if wrap then Format.pp_print_char out ')')
    out msg

let print_unop out = function
  | Flip -> CCFormat.string out "~"
  | Trans -> CCFormat.string out "^"

let print_binop out = function
  | Union -> CCFormat.string out "@<1>∪"
  | Inter -> CCFormat.string out "@<1>∩"
  | Diff -> CCFormat.string out "\\"
  | Join -> CCFormat.string out "@<1>·"
  | Concat -> CCFormat.string out "@<2>→"

let print_mult out = function
  | M_no -> CCFormat.string out "no"
  | M_one -> CCFormat.string out "one"
  | M_some -> CCFormat.string out "some"

let rec print_expr_rec p out = function
  | Const id -> ID.print out id
  | Var v -> Var.print_full out v
  | Unop (u, e) ->
    wrapf_ p P_unop out
      "@[<2>%a@ %a@]" print_unop u (print_expr_rec P_unop) e
  | Binop (o, a, b) ->
    wrapf_ p P_binop out
      "@[<2>%a@ %a @[%a@]@]"
      (print_expr_rec P_binop) a print_binop o (print_expr_rec P_binop) b
  | Comprehension (v, f) ->
    fpf out "{@[<2> %a@ | %a@]}" Var.print_full v (print_form_rec P_top) f

and print_form_rec p out = function
  | In (a,b) ->
    fpf out "@[<2>%a in @[%a@]@]"
      (print_expr_rec P_top) a (print_expr_rec P_top) b
  | Mult (m, e) -> fpf out "@[<2>%a@ %a@]" print_mult m (print_expr_rec P_top) e
  | Not f ->
    wrapf_ p P_f_not out "@[<2>not@ %a@]" (print_form_rec P_f_not) f
  | And (a,b) ->
    wrapf_ p P_f_and out "@[<2>%a && %a@]" (print_form_rec P_f_and) a (print_form_rec P_f_and) b
  | Or (a,b) ->
    wrapf_ p P_f_or out "@[<2>%a || %a@]" (print_form_rec P_f_or) a (print_form_rec P_f_or) b
  | Forall (v,f) ->
    wrapf_ p P_f_quant out "@[<2>forall %a.@ %a@]"
      Var.print_full v (print_form_rec P_f_quant) f
  | Exists (v,f) ->
    wrapf_ p P_f_quant out "@[<2>exists %a.@ %a@]"
      Var.print_full v (print_form_rec P_f_quant) f

let print_expr = print_expr_rec P_top
let print_form = print_form_rec P_top

let print_decl out d =
  fpf out "@[<hv2>%a : %d {@,[%a],@ [%a]@,}@]"
    ID.print d.decl_id d.decl_arity
    print_tuple d.decl_low print_tuple d.decl_high

let print_pb out pb =
  fpf out "@[<v2>problem {@,univ=%a@,decls=@[<v>%a@]@,goal=%a@,@]}"
    print_tuple pb.pb_univ
    (CCVector.print print_decl) pb.pb_decls
    print_form pb.pb_goal


