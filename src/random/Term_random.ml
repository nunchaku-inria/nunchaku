
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Generation of Random Terms} *)

open Nunchaku_core
module TI = TermInner

type rstate = Random.State.t
type 'a rgen = rstate -> 'a

module T = TermInner.Default
module U = TI.Util(T)
module P = TI.Print(T)
module Subst = Var.Subst

type term = T.t
type ty = T.t

let print_term = P.print

module S = struct
  let a = ID.make "a"
  let b = ID.make "b"
  let list = ID.make "list"
  let pair = ID.make "pair"

  let a0 = ID.make "a0"
  let a1 = ID.make "a1"
  let a2 = ID.make "a2"
  let f_a = ID.make "f_a"
  let g_a = ID.make "g_a"
  let h_a = ID.make "h_a"

  let b0 = ID.make "b0"
  let b1 = ID.make "b1"
  let b2 = ID.make "b2"
  let f_b = ID.make "f_b"
  let g_b = ID.make "g_b"
  let h_b = ID.make "h_b"

  let p0 = ID.make "p0"
  let p1 = ID.make "p1"
  let p2 = ID.make "p2"
  let f_p = ID.make "f_prop"
  let g_p = ID.make "g_prop"
  let h_p = ID.make "h_prop"

  let mk_pair = ID.make_full ~needs_at:true "mk_pair"
  let cons = ID.make_full ~needs_at:true "cons"
  let nil = ID.make_full ~needs_at:true "nil"
end

let app_const_ id l = U.app (U.const id) l

(* XXX invariant:
   every symbol must return a type of the shape [id var*] *)
let base_sig =
  let alpha = Var.make ~ty:U.ty_type ~name:"alpha" in
  let beta = Var.make ~ty:U.ty_type ~name:"beta" in
  let open S in
  Signature.of_list
    [ a, U.ty_type
    ; b, U.ty_type
    ; list, U.(ty_arrow ty_type ty_type)
    ; pair, U.(ty_arrow_l [ty_type; ty_type] ty_type)
    ; a0, U.ty_const a
    ; a1, U.ty_const a
    ; a2, U.ty_const a
    ; f_a, U.(ty_arrow_l [U.ty_const a; U.ty_const b] (U.ty_const a))
    ; g_a, U.(ty_arrow_l [U.ty_const a] (U.ty_const a))
    ; g_a, U.(ty_arrow_l [app_const_ list [U.ty_const a]] (U.ty_const a))
    ; b0, U.ty_const b
    ; b1, U.ty_const b
    ; b2, U.ty_const b
    ; f_b, U.(ty_arrow_l [U.ty_const b; U.ty_const a] (U.ty_const b))
    ; g_b, U.(ty_arrow_l [U.ty_const b] (U.ty_const b))
    ; h_b, U.(ty_arrow_l [app_const_ list [U.ty_const b]] (U.ty_const b))
    ; p0, U.ty_prop
    ; p1, U.ty_prop
    ; p2, U.ty_prop
    ; f_p, U.(ty_arrow_l [U.ty_const b; U.ty_prop] U.ty_prop)
    ; g_p, U.(ty_arrow_l [U.ty_const a] U.ty_prop)
    ; h_p, U.(ty_arrow_l [app_const_ list [U.ty_prop]] (U.ty_const b))
    ; mk_pair, U.(
        ty_forall_l [alpha; beta]
          (ty_arrow_l
             [U.var alpha; U.var beta]
             (ty_app (U.const pair) [U.var alpha; U.var beta])))
    ; cons,
      U.(
        let list_a = app_const_ list [U.var alpha] in
        ty_forall alpha (ty_arrow_l [U.var alpha; list_a] list_a))
    ; nil,
      U.(ty_forall alpha (app_const_ list [U.var alpha]))
    ]

type id_plus =
  | I of ID.t
  | Prop

let compare_id_plus i1 i2 = match i1, i2 with
  | Prop, Prop -> 0
  | I i1, I i2 -> ID.compare i1 i2
  | I _, Prop -> 1
  | Prop, I _ -> -1

type build_rule =
  | AppID of ID.t
  | AppBuiltin of (term list -> term)

(* rule to build some type:
   to build [target], need to create arguments [args]. All variables occuring
   in [goals] also occur in [target] *)
type backward_rule = {
  build: build_rule; (* symbol that has this type *)
  vars: ty Var.t list; (* list of free vars *)
  target: ty;
  goals: ty list;
}

let pp_build_rule out = function
  | AppID id -> ID.print out id
  | AppBuiltin _ -> CCFormat.string out "<builtin>"

let pp_rule out r =
  Format.fprintf out "(@[<2>%a :-@ @[<hv>%a@]@ using %a@])"
    P.print r.target (CCFormat.list ~start:"" ~stop:"" P.print) r.goals
    pp_build_rule r.build

type backward_rules = backward_rule list

(* is the rule proper? *)
let check_rule r =
  let vars_t = U.free_vars r.target in
  let vars_g =
    Sequence.of_list r.goals
    |> Sequence.flat_map (U.to_seq_free_vars ?bound:None)
    |> U.VarSet.of_seq
  in
  U.VarSet.equal vars_t (U.VarSet.of_list r.vars) &&
  U.VarSet.subset vars_g vars_t

let mk_imply = function [a;b] -> U.imply a b | _ -> assert false
let mk_equiv = function [a;b] -> U.equiv a b | _ -> assert false
let mk_not = function [a] -> U.not_ a | _ -> assert false

(* XXX: we do not have a rule for [=], because the rule would not be
   well-formed (type a -> a -> prop) *)
let builtin_rules =
  [ {target=U.ty_prop; goals=[U.ty_prop; U.ty_prop]; vars=[]; build=AppBuiltin mk_imply}
  ; {target=U.ty_prop; goals=[U.ty_prop; U.ty_prop]; vars=[]; build=AppBuiltin mk_equiv}
  ; {target=U.ty_prop; goals=[U.ty_prop]; vars=[]; build=AppBuiltin mk_not}
  ; {target=U.ty_prop; goals=[U.ty_prop; U.ty_prop]; vars=[]; build=AppBuiltin U.and_}
  ; {target=U.ty_prop; goals=[U.ty_prop; U.ty_prop]; vars=[]; build=AppBuiltin U.or_}
  ]

(* rename a rule with fresh variables *)
let rename_rule r =
  let subst, vars = Utils.fold_map Subst.rename_var Subst.empty r.vars in
  { r with
      vars;
      target=U.eval_renaming ~subst r.target;
      goals=List.map (U.eval_renaming ~subst) r.goals;
  }

(* from a signature, build backward rules *)
let mk_rules sigma : backward_rules =
  ID.Map.fold
    (fun id ty acc ->
       let vars, args, ret = U.ty_unfold ty in
       assert (List.for_all (fun a -> U.ty_is_Type (Var.ty a)) vars);
       let r = { build=AppID id; vars; target=ret; goals=args} in
       if not (check_rule r)
       then failwith (Utils.err_sprintf "@[invalid rule@ %a@]" pp_rule r);
       r :: acc
    )
    sigma
    builtin_rules

(* basic set of rules *)
let rules : backward_rules = mk_rules base_sig

(** {2 Generators} *)

module G = QCheck.Gen

let sized' g = G.(3 -- 50 >>= g)

(* TODO: polymorphism? *)

(* TODO: generate function types
   - to build a, build (b -> a) and b
   - to build the term we need a set of bound variables to use *)
let ty =
  let base = G.oneofl [U.const S.a; U.const S.b; U.ty_prop] in
  let pair' a b = app_const_ S.pair [a;b] in
  let list' a = app_const_ S.list [a] in
  let fun1 = U.ty_arrow in
  let fun2 a b c = U.ty_arrow_l [a;b] c in
  let open G in
  fix
     (fun self n ->
        if n=0
        then base
        else
          frequency
            [ 3, base
            ; 1, return list' <*> self (n-1)
            ; 1, return pair' <*> self (n-1) <*> self (n-1)
            ; 1, return fun1 <*> self (n-1) <*> self (n-1)
            ; 1, return fun2 <*> self (n-1) <*> self (n-1) <*> self (n-1)
            ])
  |> sized'

(* recursive generation of a term of type [ty] *)
let rec gen_ rules ty subst size =
  let possible_rules =
    CCList.filter_map
      (fun r ->
         (* avoid variable collision *)
         let r = rename_rule r in
         match U.match_ ~subst2:subst r.target ty with
           | None -> None
           | Some subst' ->
             let subst = Subst.concat subst' ~into:subst in
             let freq = match r.goals with
               | [] -> 4
               | [_] -> if size<3 then 1 else 5
               | _ -> if size<3 then 1 else 8
             in
             Some (freq, (subst, r)))
      rules
  in
  assert (possible_rules <> []);
  let open G in
  (* pick a rule randomly *)
  frequencyl possible_rules >>= fun (subst, r) ->
  (* generate a term for each goal type *)
  let size' = size - 2 * List.length r.goals in
  gen_l_ rules r.goals subst size' >|= fun l ->
  (* apply [r.id] to the terms *)
  match r.build with
    | AppID id -> app_const_ id l
    | AppBuiltin f -> f l

(* generate a list of terms of types [ty_l] *)
and gen_l_ rules ty_l subst size = match ty_l with
  | [] -> G.return []
  | ty :: ty_tail ->
    let open G in
    gen_ rules ty subst size >>= fun t ->
    gen_l_ rules ty_tail subst size >|= fun tail ->
    t :: tail

let of_ty ty = sized' (gen_ rules ty Subst.empty)

let prop = of_ty U.ty_prop

let random = G.(ty >>= of_ty)

let mk_arbitrary_ g =
  QCheck.make
    ~print:(CCFormat.to_string print_term)
    ~small:U.size
    g

let arbitrary = mk_arbitrary_ random
let arbitrary_ty = mk_arbitrary_ ty
let arbitrary_prop = mk_arbitrary_ prop

let generate rand g = g rand

let mk_rand() = Random.State.make_self_init ()

let generate_l ?n ?(rand=mk_rand()) g =
  let n = CCOpt.get_lazy (fun () -> G.(1 -- 50) rand) n in
  G.list_repeat n g rand
