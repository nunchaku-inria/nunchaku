(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Relational FO Logic} *)

(** {2 Types} *)

type atom_name = ID.t

(* the portion of the universe concerned with this atom name *)
type sub_universe = {
  su_name: atom_name;
  su_min_card: int;
  su_max_card: int option;
}

(* an indexed atom. It lives in the sub-universe of the same name *)
type atom = {
  a_sub_universe: sub_universe;
  a_index: int; (* invariant: a_index < a_sub_universe.su_max_card *)
}

type tuple = atom list

type tuple_set =
  | TS_list of tuple list (* explicit set *)
  | TS_product of tuple_set list (* cartesian product *)
  | TS_all of sub_universe (* all the atoms of this sub-universe *)

type unop =
  | Flip (** flip p x y <=> p y x *)
  | Trans (** trans p == transitive closure *)

type binop =
  | Union
  | Inter
  | Diff
  | Join
  | Product

type mult =
  | M_no
  | M_one
  | M_lone
  | M_some

type expr =
  | None_ (* empty set *)
  | Const of ID.t
  | Tuple_set of tuple_set
  | Var of var
  | Unop of unop * expr
  | Binop of binop * expr * expr
  | If of form * expr * expr
  | Comprehension of var * form
  | Let of var * expr * expr

and var_ty = sub_universe

and var = var_ty Var.t

and form =
  | True
  | False
  | Eq of expr * expr
  | In of expr * expr
  | Mult of mult * expr
  | Not of form
  | And of form list
  | Or of form list
  | Imply of form * form
  | Equiv of form * form
  | Forall of var * form
  | Exists of var * form
  | F_let of var * expr * form
  | F_if of form * form * form
  | Int_op of int_op * int_expr * int_expr

(* NOTE: only the subset we're interested in *)
and int_op =
  | IO_leq

(* NOTE: only the subset we're interested in *)
and int_expr =
  | IE_card of expr
  | IE_sum of expr
  | IE_cst of int

type decl = {
  decl_id: ID.t;
  decl_arity: int;
  decl_dom: sub_universe list;
  decl_low: tuple_set; (* lower bound *)
  decl_high: tuple_set; (* higher bound *)
}

type universe = {
  univ_prop: sub_universe; (* a special sub-universe for pseudo-prop *)
  univ_l: sub_universe list;
}

type problem = {
  pb_univ: universe;
  pb_decls: decl ID.Map.t;
  pb_goal: form list; (* conjunction *)
  pb_meta: ProblemMetadata.t;
}

(** {2 Helpers} *)

let unop o a = Unop (o,a)
let binop o a b = Binop (o,a,b)
let mult m a = Mult (m,a)

let su_make ?(min_card=0) ?max_card:su_max_card su_name =
  begin match su_max_card with
    | Some n when n <= 0 -> invalid_arg "su_make"
    | _ -> ()
  end;
  { su_name; su_min_card = min_card; su_max_card }

let su_hash s = ID.hash s.su_name
let su_compare s1 s2 =
  CCOrd.(
    ID.compare s1.su_name s2.su_name
    <?> (int, s1.su_min_card, s2.su_min_card)
    <?> (option int, s1.su_max_card, s2.su_max_card)
  )
let su_equal s1 s2 = su_compare s1 s2 = 0

let ts_list l = TS_list l
let ts_all s = TS_all s
let ts_product l =
  let as_prod_ ts = match ts with
    | TS_all _
    | TS_list _ -> [ts]
    | TS_product l -> l
  in
  match CCList.flat_map as_prod_ l with
    | [x] -> x
    | [] -> TS_product []
    | l -> TS_product l

let flip a = unop Flip a
let trans a = unop Trans a
let const id = Const id
let var v = Var v
let tuple_set s = Tuple_set s
let union = binop Union
let inter = binop Inter
let diff = binop Diff
let join = binop Join
let product = binop Product
let if_ a b c = If (a,b,c)
let comprehension v f = Comprehension (v,f)
let let_ v t u = Let (v,t,u)

let true_ = True
let false_ = False
let in_ a b = In (a,b)
let eq a b = Eq (a,b)
let no = mult M_no
let one = mult M_one
let some = mult M_some
let not_ = function
  | Not a -> a
  | a -> Not a
let and_l = function
  | [] -> true_
  | [a] -> a
  | l -> And l
let and_ a b = and_l [a;b]
let or_l = function
  | [] -> false_
  | [a] -> a
  | l -> Or l
let or_ a b = or_l [a;b]
let imply a b = Imply (a,b)
let equiv a b = Equiv (a,b)
let for_all v f = Forall (v,f)
let for_all_l = List.fold_right for_all
let exists v f = Exists (v,f)
let exists_l = List.fold_right exists
let f_let v a b = F_let (v,a,b)
let f_if a b c = F_if (a,b,c)

let int_op op a b = Int_op (op, a, b)
let int_leq = int_op IO_leq

let int_sum e = IE_sum e
let int_card e = IE_card e
let int_const i = IE_cst i

let atom su i = { a_sub_universe=su; a_index=i }
let atom_cmp a1 a2 =
  CCOrd.(
    su_compare a1.a_sub_universe a2.a_sub_universe
    <?> (int, a1.a_index, a2.a_index)
  )
let atom_eq a1 a2 = atom_cmp a1 a2 = 0

let mk_problem ~meta:pb_meta ~univ:pb_univ ~decls:pb_decls ~goal:pb_goal =
  { pb_meta; pb_univ; pb_decls; pb_goal; }

(** {2 IO} *)

let fpf = Format.fprintf

let pp_list ~sep pp = Utils.pp_list ~sep pp

let pp_atom out a =
  fpf out "%a_%d" ID.pp_name a.a_sub_universe.su_name a.a_index

let pp_sub_universe out s =
  let pp_card out = function
    | (m, None) -> Format.fprintf out "%d.." m
    | (m, Some n) -> Format.fprintf out "%d..%d" m n
  in
  fpf out "%a_%a" ID.pp_name s.su_name pp_card (s.su_min_card, s.su_max_card)

let pp_tuple out (t:tuple) =
  fpf out "(@[%a@])" (pp_list ~sep:"," pp_atom) t

let rec pp_tuple_set out (s:tuple_set) = match s with
  | TS_product l ->
    fpf out "(@[<hv>%a@])" (pp_list ~sep:" * " pp_tuple_set) l
  | TS_list l ->
    fpf out "{@[<hv>%a@]}" (pp_list ~sep:", " pp_tuple) l
  | TS_all s -> pp_sub_universe out s

(* precedence level *)
type prec =
  | P_unop
  | P_binop of binop
  | P_f_not
  | P_f_and
  | P_f_or
  | P_f_quant
  | P_top

let compare_prec : prec CCOrd.t = Pervasives.compare

let left_assoc = function
  | P_binop Diff -> true
  | P_top
  | P_binop _
  | P_f_and
  | P_f_not
  | P_f_or
  | P_f_quant
  | P_unop -> false

(* if [p1 < p2], then pp [msg] surrounded with parenthesis, else pp [msg] *)
let wrapf_ p1 p2 out msg =
  let c = compare_prec p1 p2 in
  let wrap = if left_assoc p1 then c <= 0 else c<0 in
  if wrap then Format.pp_print_char out '(';
  Format.kfprintf
    (fun out -> if wrap then Format.pp_print_char out ')')
    out msg

let pp_unop out = function
  | Flip -> CCFormat.string out "~"
  | Trans -> CCFormat.string out "^"

let pp_binop out = function
  | Union -> fpf out "@<1>∪"
  | Inter -> fpf out "@<1>∩"
  | Diff -> CCFormat.string out "\\"
  | Join -> fpf out "@<1>·"
  | Product -> fpf out "@<2>→"

let pp_mult out = function
  | M_no -> CCFormat.string out "no"
  | M_one -> CCFormat.string out "one"
  | M_lone -> CCFormat.string out "lone"
  | M_some -> CCFormat.string out "some"

let rec pp_expr_rec p out = function
  | None_ -> fpf out "none"
  | Const id -> ID.pp out id
  | Tuple_set s -> pp_tuple_set out s
  | Var v -> Var.pp_full out v
  | Unop (u, e) ->
    wrapf_ p P_unop out
      "@[<2>%a@ %a@]" pp_unop u (pp_expr_rec P_unop) e
  | Binop (o, a, b) ->
    wrapf_ p (P_binop o) out
      "@[<2>%a@ %a @[%a@]@]"
      (pp_expr_rec (P_binop o)) a
      pp_binop o
      (pp_expr_rec (P_binop o)) b
  | If (a,b,c) ->
    fpf out "@[<hv2>if @[%a@]@ then @[%a@]@ else @[%a@]@]"
      (pp_form_rec P_top) a (pp_expr_rec P_top) b (pp_expr_rec P_top) c
  | Comprehension (v, f) ->
    fpf out "{@[<2> %a@ | %a@]}" pp_typed_var v (pp_form_rec P_top) f
  | Let (v,t,u) ->
    fpf out "@[<2>let @[%a := %a@]@ in @[%a@]@]" pp_typed_var v
      (pp_expr_rec P_top) t (pp_expr_rec p) u

and pp_int_expr out = function
  | IE_sum e -> fpf out "(@[<1>sum@ %a@])" (pp_expr_rec P_top) e
  | IE_card e -> fpf out "#(@[%a@])" (pp_expr_rec P_top) e
  | IE_cst i -> fpf out "%d" i

and pp_form_rec p out = function
  | True -> CCFormat.string out "true"
  | False -> CCFormat.string out "false"
  | Eq (a,b) ->
    fpf out "@[@[%a@]@ @[<2>=@ @[%a@]@]@]"
      (pp_expr_rec P_top) a (pp_expr_rec P_top) b
  | In (a,b) ->
    fpf out "@[@[%a@]@ @[<2>in@ @[%a@]@]@]"
      (pp_expr_rec P_top) a (pp_expr_rec P_top) b
  | Mult (m, e) -> fpf out "@[<2>%a@ @[%a@]@]" pp_mult m (pp_expr_rec P_top) e
  | Not f ->
    wrapf_ p P_f_not out "@[<2>not@ @[%a@]@]" (pp_form_rec P_f_not) f
  | And l ->
    wrapf_ p P_f_and out "@[<hv>%a@]"
      (pp_infix_list (pp_form_rec P_f_and) "&&") l
  | Or l ->
    wrapf_ p P_f_and out "@[<hv>%a@]"
      (pp_infix_list (pp_form_rec P_f_or) "||") l
  | Imply (a,b) ->
    wrapf_ p P_f_or out "(@[<hv>%a@ => %a@]"
      (pp_form_rec P_f_or) a (pp_form_rec P_f_or) b
  | Equiv (a,b) ->
    wrapf_ p P_f_or out "@[@[%a@]@ <=> %a@]"
      (pp_form_rec P_f_or) a (pp_form_rec P_f_or) b
  | Forall (v,f) ->
    wrapf_ p P_f_quant out "@[<2>forall @[%a@].@ @[%a@]@]"
      pp_typed_var v (pp_form_rec P_f_quant) f
  | Exists (v,f) ->
    wrapf_ p P_f_quant out "@[<2>exists @[%a@].@ @[%a@]@]"
      pp_typed_var v (pp_form_rec P_f_quant) f
  | F_let (v,a,b) ->
    wrapf_ p P_f_quant out "@[<2>let @[%a := %a@].@ @[%a@]@]"
      pp_typed_var v (pp_expr_rec P_top) a (pp_form_rec P_f_quant) b
  | F_if (a,b,c) ->
    wrapf_ p P_f_and out "@[<hv2>if %a@ then %a@ else %a@]"
      (pp_form_rec P_top) a
      (pp_form_rec P_top) b
      (pp_form_rec P_f_and) c
  | Int_op (IO_leq, a, b) ->
    fpf out "(@[%a@ =< %a@])" pp_int_expr a pp_int_expr b

and pp_infix_list pform s out l = match l with
  | [] -> assert false
  | [t] -> pform out t
  | t :: l' ->
    fpf out "@[%a@]@ %s %a"
      pform t s (pp_infix_list pform s) l'

and pp_var_ty out su = ID.pp out su.su_name

and pp_typed_var out v =
  fpf out "(@[<2>%a :@ %a@])"
    Var.pp_full v pp_var_ty (Var.ty v)

let pp_expr = pp_expr_rec P_top
let pp_form = pp_form_rec P_top

let pp_universe out u =
  let l = u.univ_prop :: u.univ_l in
  fpf out "@[%a@]" (pp_list ~sep:" + " pp_sub_universe) l

let pp_decl out d =
  fpf out "@[<hv2>%a :@ arity=%d@ low=%a@ high=%a@]"
    ID.pp d.decl_id d.decl_arity
    pp_tuple_set d.decl_low
    pp_tuple_set d.decl_high

let pp_problem out pb =
  fpf out "@[<v2>problem {@,univ=%a@,decls=[@[<v>%a@]]@,goal=@[<hv>%a@]@,@]}"
    pp_universe pb.pb_univ
    (Utils.pp_seq pp_decl) (ID.Map.values pb.pb_decls)
    (pp_list ~sep:" && " pp_form) pb.pb_goal
