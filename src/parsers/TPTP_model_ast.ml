
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Simple Model AST} *)

open Nunchaku_core

module T = FO_tptp

type name = string
type id = string
type var = string

type term =
  | App of id * term list
  | Var of var
  | Forall of var * term
  | And of term * term
  | Or of term * term
  | Not of term
  | Atom of term
  | Eq of term * term
  | Equiv of term * term
  | True
  | False

type statement =
  | Fi_domain of name * var * id list (* forall X. X=a1 | ... | X=an *)
  | Fi_functors of name * id * var list * (var list * term list * term) list
  | Fi_predicates of name * id * var list * (var list * term list * term) list

let var v = Var v
let app id l = App (id,l)
let const id = app id []

let forall v f = Forall (v,f)
let or_ a b = Or(a,b)
let and_ a b = And(a,b)
let not_ = function
  | True -> False
  | False -> True
  | a -> Not a
let eq a b = Eq(a,b)
let equiv a b = Equiv(a,b)
let atom t = Atom t
let true_ = True
let false_ = False

module Conv = struct
  let failf m = Parsing_utils.parse_error_ m

  let as_forall_ = function
    | Forall (v,f) -> v, f
    | _ -> failf "expected forall"

  let rec open_forall = function
    | Forall (v,f) ->
      let vars, f' = open_forall f in
      v :: vars, f'
    | t -> [], t

  let rec as_or_ = function
    | Or (a,b) -> List.rev_append (as_or_ a) (as_or_ b)
    | (Atom _ | Eq _ ) as f -> [f]
    | _ -> failf "expected conjunction"

  let as_id_eqn_of_ v = function
    | Eq (Var v', App (rhs, _)) when v=v' -> rhs
    | _ -> failf "expected equation with LHS=%s" v

  let as_ground_term_ = function
    | App (id, args) -> id, args
    | _ -> failf "expected ground term"

  let as_eqn_ t =
    let vars, t = open_forall t in
    match t with
      | Eq (lhs,rhs) ->
        let id, args = as_ground_term_ lhs in
        id, (vars, args, rhs)
      | _ -> failf "expected equation"

  let as_atom_ t =
    let vars, t = open_forall t in
    let rec aux = function
      | Not f ->
        let id, (vars, args, rhs) = aux f in
        id, (vars, args, not_ rhs)
      | Atom (App (id, args)) ->
        id, (vars, args, true_)
      | Equiv (lhs, rhs) ->
        let id, args = as_ground_term_ lhs in
        id, (vars, args, rhs)
      | _ -> failf "expected signed atom"
    in
    aux t
end

let mk_fi_domain name (f:term) : statement =
  let v, l = Conv.as_forall_ f in
  let l = List.map (Conv.as_id_eqn_of_ v) (Conv.as_or_ l) in
  Fi_domain (name, v, l)

let mk_fi_functors name vars (l:term list) : statement =
  let l = List.map Conv.as_eqn_ l in
  let id = match l with
    | [] -> assert false
    | (id, _) :: _ -> id
  in
  Fi_functors (name, id, vars, List.map snd l)

let mk_fi_predicates name vars (l:term list) : statement =
  let l = List.map Conv.as_atom_ l in
  let id = match l with
    | [] -> assert false
    | (id, _) :: _ -> id
  in
  Fi_predicates (name, id, vars, List.map snd l)

let pp_list_ pp = CCFormat.list ~sep:" " ~start:"" ~stop:"" pp

let rec pp_term out = function
  | Var v -> CCFormat.string out v
  | App (id,[]) -> CCFormat.string out id
  | App (id,l) -> Format.fprintf out "(@[%s@ %a@])" id (pp_list_ pp_term) l
  | Forall (v,f) -> Format.fprintf out "(@[forall %s.@ %a@])" v pp_term f
  | And (a,b) -> Format.fprintf out "(@[and %a@ %a@])" pp_term a pp_term b
  | Or (a,b)-> Format.fprintf out "(@[or@ %a@ %a@])" pp_term a pp_term b
  | Not t -> Format.fprintf out "(@[not@ %a@])" pp_term t
  | Atom t -> pp_term out t
  | Eq (a,b) -> Format.fprintf out "(@[=@ %a@ %a@])" pp_term a pp_term b
  | Equiv (a,b) -> Format.fprintf out "(@[<=>@ %a@ %a@])" pp_term a pp_term b
  | True -> CCFormat.string out "true"
  | False -> CCFormat.string out "false"

let pp_statement out st =
  let pp_vars out = function
    | [] -> ()
    | vars -> Format.fprintf out "![@[%a@]]:@ " (pp_list_ CCFormat.string) vars
  in
  match st with
  | Fi_domain (_, v, l) ->
    Format.fprintf out "(@[<1>domain %s in@ [@[%a@]]@])."
      v (pp_list_ CCFormat.string) l
  | Fi_functors (_, id, vars, l) ->
    let pp_eqn out (vars',args,rhs) =
      Format.fprintf out "(@[%a%s(%a)@ = %a@])"
        pp_vars vars' id (pp_list_ pp_term) args pp_term rhs
    in
    Format.fprintf out "(@[<1>functors for %s@ @[%a[@[%a@]]@]@])."
      id pp_vars vars (pp_list_ pp_eqn) l
  | Fi_predicates (_, id, vars, l) ->
    let pp_pred out args = Format.fprintf out "%s(%a)" id (pp_list_ pp_term) args in
    let pp_pred out (vars',args,rhs) =
      Format.fprintf out "(%a@[%a <=> %a@])" pp_vars vars' pp_pred args pp_term rhs
    in
    Format.fprintf out "(@[<1>predicates for %s@ @[%a[@[%a@]]@]@])."
      id pp_vars vars (pp_list_ pp_pred) l

let pp_statements out =
  Format.fprintf out "[@[<hv>%a@]]"
    (CCFormat.list ~start:"" ~stop:"" ~sep:" " pp_statement)

(** {2 Conversion to Model} *)

let to_model (l:statement list) : (T.term, T.ty) Model.t =
  let module M = Model in
  (* unfailing name -> ID *)
  let id_of_name_ i : ID.t option =
    try Some (ID.Erase.of_name T.erase i)
    with Not_found -> None
  in
  (* some names were not in the input, such as constants *)
  let get_or_create_id i =
    try ID.Erase.of_name T.erase i
    with Not_found ->
      let id = ID.make i in
      ID.Erase.add_name T.erase i id;
      id
  in
  (* convert a term back *)
  let rec term_to_tptp subst (t:term) : T.term = match t with
    | App (id, l) ->
      let subst _ = Conv.failf "no variable allowed in sub-term under %s" id in
      T.app (get_or_create_id id) (List.map (term_to_tptp subst) l)
    | Var v -> subst v
    | True -> T.true_
    | False -> T.false_
    | _ -> Conv.failf "cannot convert `@[%a@]` to term" pp_term t
  in
  (* convert a list of cases into a Model.DT *)
  let cases_to_dt input_vars l =
    (* create fresh variables *)
    let vars = match l with
      | [] -> assert false
      | (_, args, _) :: _ ->
        List.mapi (fun i _ -> Var.makef ~ty:T.Unitype "v%d" i) args
    in
    assert (List.length vars >= List.length input_vars);
    if vars=[]
    then match l with
      | [_, [], rhs] ->
        let subst v = Conv.failf "variable %s not in scope" v in
        `Const (term_to_tptp subst rhs)
      | _ -> assert false
    else (
      let l =
        List.map
          (fun (input_vars',args,rhs) ->
             assert (List.length args = List.length vars);
             let vars_seen = ref [] in
             (* map members of [input_vars] to [vars] *)
             let subst i v =
               if List.mem_assoc v !vars_seen
               then List.assoc v !vars_seen
               else if (List.mem v input_vars || List.mem v input_vars') && i>=0
               then (
                 let v' = T.var (List.nth vars i) in
                 vars_seen := (v, v') :: !vars_seen;
                 v'
               )
               else Conv.failf "variable %s not in scope" v
             in
             let args = List.mapi (fun i -> term_to_tptp (subst i)) args in
             let rhs = term_to_tptp (subst ~-1) rhs in
             let conds = List.combine vars args in
             conds, rhs)
          l
      in
      let else_ = T.undefined_atom (List.map T.var vars) in
      let dt = M.DT.test l ~else_ in
      `Fun (vars, dt)
    )
  in
  (* add one statement to the model *)
  let add_st m st : _ M.t = match st with
    | Fi_domain (_, _, l) ->
      (* trivial domain *)
      let l = List.map get_or_create_id l in
      M.add_finite_type m T.Unitype l
    | Fi_functors (_, name, vars, l) ->
      begin match id_of_name_ name with
        | None ->
          Utils.debugf 2 "failed to map `%s` to a known ID" (fun k->k name);
          m
        | Some id ->
          begin match cases_to_dt vars l with
            | `Const rhs -> M.add_const m (T.const id, rhs, M.Symbol_fun)
            | `Fun (vars, dt) ->
              M.add_fun m (T.const id, vars, dt, M.Symbol_fun)
          end
      end
    | Fi_predicates (_, name, vars, l) ->
      begin match id_of_name_ name with
        | None ->
          Utils.debugf 2 "failed to map `%s` to a known ID" (fun k->k name);
          m
        | Some id ->
          begin match cases_to_dt vars l with
            | `Const rhs -> M.add_const m (T.const id, rhs, M.Symbol_prop)
            | `Fun (vars, dt) ->
              M.add_fun m (T.const id, vars, dt, M.Symbol_prop)
          end
      end
  in
  List.fold_left add_st M.empty l
