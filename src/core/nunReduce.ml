
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Reductions, including Beta Reduction} *)

module ID = NunID
module Var = NunVar
module TI = NunTerm_intf
module T = NunTerm_ho
module Subst = Var.Subst
module U = T.SubstUtil

type ('t, 'inv) build = ('t, 'inv) NunTerm_ho.build

(* low level implementation *)
module Full = struct
  type 't subst = ('t, 't) Subst.t

  (* head applied to args, in environment subst *)
  type 't state = {
    head: 't;
    args: 't list;
    subst: 't subst;
  }

  let push_args ~st l = l @ st.args

  (* convert a state back to a term *)
  let term_of_state ~build st =
    let head = U.eval ~build ~subst:st.subst st.head in
    match st.args with
      | [] -> head
      | l ->
          let l = List.map (U.eval ~build ~subst:st.subst) l in
          T.app ~build head l

  type 't bool_ =
    | BTrue
    | BFalse
    | BPartial of 't

  type 't eval = subst:'t subst -> 't -> 't

  (* evaluate boolean operators. Subterms are evaluated with [eval] *)
  let rec eval_bool
  : type t inv. build:(t,inv)T.build -> eval:t eval -> subst:t subst -> t -> t bool_
  = fun ~build ~eval ~subst t ->
    let module B = NunBuiltin.T in
    (* base case *)
    let basic ~subst t =
      let t' = eval ~subst t in
      match build.TI.b_repr t' with
      | TI.AppBuiltin (B.True, _) -> BTrue
      | TI.AppBuiltin (B.False, _) -> BFalse
      | _ -> BPartial t'
    in
    match build.TI.b_repr t with
    | TI.AppBuiltin (B.True, _) -> BTrue
    | TI.AppBuiltin (B.False, _) -> BFalse
    | TI.AppBuiltin (B.And, l) ->
        eval_and_l ~build ~eval ~default:t ~subst l
    | TI.AppBuiltin (B.Or, l) ->
        eval_or_l ~build ~eval ~default:t ~subst l
    | TI.AppBuiltin (B.Imply, [a;b]) ->
        (* truth table *)
        begin match eval_bool ~build ~eval ~subst a, eval_bool ~build ~eval ~subst b with
        | _, BTrue
        | BFalse, _ -> BTrue
        | BTrue, BFalse -> BFalse
        | BPartial _, _
        | _, BPartial _ -> BPartial t
        end
    | TI.AppBuiltin (B.Equiv, [a;b]) ->
        (* truth table *)
        begin match eval_bool ~build ~eval ~subst a, eval_bool ~build ~eval ~subst b with
        | BTrue, BTrue
        | BFalse, BFalse -> BTrue
        | BTrue, BFalse
        | BFalse, BTrue -> BFalse
        | BPartial _, _
        | _, BPartial _ -> BPartial t
        end
    | TI.AppBuiltin (B.Eq, [a;b]) ->
        let a = eval ~subst a in
        let b = eval ~subst b in
        (* TODO: if [a] and [b] fully evaluated, return False? *)
        if U.equal ~build ~subst a b
        then BTrue
        else BPartial (T.eq ~build a b)
    | TI.AppBuiltin (B.Not, [f]) ->
        begin match eval_bool ~build ~eval ~subst f with
        | BTrue -> BFalse
        | BFalse -> BTrue
        | BPartial t -> BPartial (T.app_builtin ~build B.Not [t])
        end
    | TI.AppBuiltin ((B.Imply | B.Equiv | B.Eq | B.Not), _) ->
        assert false (* wrong arity *)
    | TI.AppBuiltin ((B.Ite | B.DataSelect _ | B.DataTest _), _) ->
        invalid_arg "not boolean operators"
    | TI.TyVar _ -> basic ~subst t
    | TI.Bind _ -> basic ~subst t
    | TI.Const _
    | TI.Var _
    | TI.App _
    | TI.Let _
    | TI.Match _
    | TI.TyBuiltin _
    | TI.TyArrow (_,_) -> basic ~subst t
    | TI.TyMeta _ -> BPartial t

  and eval_and_l
  : type t inv. build:(t,inv)T.build -> eval:t eval ->
      default:t -> subst:t subst -> t list -> t bool_
  = fun ~build ~eval ~default ~subst l -> match l with
    | [] -> BTrue
    | t :: l' ->
        match eval_bool ~build ~eval ~subst t with
        | BTrue -> eval_and_l ~build ~eval ~default ~subst l'
        | BFalse -> BFalse
        | BPartial _ -> BPartial default

  and eval_or_l
  : type t inv. build:(t,inv)T.build -> eval:t eval ->
      default:t -> subst:t subst -> t list -> t bool_
  = fun ~build ~eval ~default ~subst l -> match l with
    | [] -> BFalse
    | t :: l' ->
        match eval_bool ~build ~eval ~subst t with
        | BTrue -> BTrue
        | BFalse -> eval_or_l ~build ~eval ~default ~subst l'
        | BPartial _ -> BPartial default

  (* evaluate [b l] using [eval] *)
  let eval_app_builtin
  : type t inv.
      build:(t,inv) T.build -> eval:(t state -> t state) ->
      NunBuiltin.T.t -> t list -> st:t state -> t state
  = fun ~build ~eval b l ~st ->
    let module B = NunBuiltin.T in
    (* auxiliary function *)
    let eval_term ~subst t =
      term_of_state ~build (eval {args=[]; head=t; subst}) in
    match b, l with
    | (B.True | B.False), _ -> st (* normal form *)
    | (B.And | B.Eq | B.Imply | B.Equiv | B.Not | B.Or), _ ->
        begin match eval_bool ~build ~eval:eval_term ~subst:st.subst st.head with
        | BTrue -> {st with head=T.builtin ~build B.True}
        | BFalse -> {st with head=T.builtin ~build B.False}
        | BPartial t -> {st with head=t}
        end
    | B.Ite, [a;b;c] ->
        (* special case: ite can reduce further if [a] reduces to
          a boolean, because then branches can be functions *)
        begin match eval_bool ~build ~eval:eval_term ~subst:st.subst a with
        | BTrue -> eval {st with head=b}
        | BFalse -> eval {st with head=c}
        | BPartial a' -> {st with head=T.ite ~build a' b c}
        end
    | B.DataTest _, [_] ->
        NunUtils.not_implemented "evaluation of DataTest"
    | B.DataSelect (_,_), [_] ->
        NunUtils.not_implemented "evaluation of DataSelect"
    | (B.Ite | B.DataSelect _ | B.DataTest _),_ -> assert false

  (* see whether [st] matches a case in [m] *)
  let lookup_case_ ~build st m = match build.TI.b_repr st.head with
    | TI.Const id ->
        begin try
          let vars, rhs = ID.Map.find id m in
          (* it matches! arity should match too, otherwise the
           term is ill-typed *)
          let subst = Subst.add_list ~subst:st.subst vars st.args in
          Some (rhs, subst)
        with Not_found ->
          None
        end
    | _ -> None

  (* reduce until the head is not a function *)
  let rec whnf_
  : type t inv. build:(t,inv) T.build -> t state -> t state
  = fun ~build st -> match build.TI.b_repr st.head with
    | TI.Const _ -> st
    | TI.AppBuiltin ((NunBuiltin.T.False | NunBuiltin.T.True), _) -> st
    | TI.AppBuiltin (b, l) ->
        eval_app_builtin ~build ~eval:(whnf_ ~build) ~st b l
    | TI.Var v ->
        (* dereference, if any *)
        begin match Subst.find ~subst:st.subst v with
        | None -> st
        | Some t -> whnf_ ~build {st with head=t}
        end
    | TI.TyVar v ->
        (* dereference, if any *)
        begin match Subst.find ~subst:st.subst v with
        | None -> st
        | Some t -> whnf_ ~build {st with head=t}
        end
    | TI.App (f, l) ->
        whnf_ ~build {st with head=f; args=push_args ~st l}
    | TI.Bind (TI.Fun, v,body) ->
        begin match st.args with
        | [] -> st
        | a :: args' ->
            (* beta-redex *)
            whnf_ ~build {
              head=body;
              args=args';
              subst=Subst.add ~subst:st.subst v a
            }
        end
    | TI.Match (t, l) ->
        let st_t = whnf_ ~build {head=t; args=[]; subst=st.subst; } in
        (* see whether [st] matches some case *)
        begin match lookup_case_ ~build st_t l with
          | None ->
              (* just replace the head *)
              { st with head=T.match_with ~build (term_of_state ~build st_t) l }
          | Some (rhs, subst) ->
              whnf_ ~build {st with head=rhs; subst; }
        end
    | TI.Bind (TI.TyForall, _, _) -> assert false
    | TI.Bind ((TI.Forall | TI.Exists), _, _) -> st
    | TI.Let _
    | TI.TyBuiltin _
    | TI.TyArrow _ -> st
    | TI.TyMeta _ -> assert false

  let whnf ~build ?(subst=Subst.empty) t args =
    let st = whnf_ ~build {head=t; args; subst; } in
    st.head, st.args, st.subst

  (* strong normal form *)
  let rec snf_
  : type t inv. build:(t,inv) build -> t state -> t state
  = fun ~build st ->
    (* first, head reduction *)
    let st = whnf_ ~build st in
    (* then, reduce subterms *)
    match build.TI.b_repr st.head with
    | TI.TyBuiltin _
    | TI.Const _
    | TI.AppBuiltin (_,[]) -> st
    | TI.AppBuiltin (b,l) ->
        let l = List.map (snf_term ~build ~subst:st.subst) l in
        eval_app_builtin ~build ~eval:(snf_ ~build) ~st b l
    | TI.Bind (TI.TyForall,_,_) -> st
    | TI.TyArrow (_,_) ->
        st (* NOTE: depend types might require beta-reduction in types *)
    | TI.Var v ->
        assert (not (Subst.mem ~subst:st.subst v));
        st
    | TI.TyVar v ->
        assert (not (Subst.mem ~subst:st.subst v));
        st
    | TI.App (_,_) -> assert false  (* not WHNF *)
    | TI.Bind (TI.Fun, v, body) ->
        assert (st.args = []);
        enter_snf_ ~build st v body (fun v body -> T.fun_ ~build v body)
    | TI.Bind (b, v,t) ->
        enter_snf_ ~build st v t (fun v t -> T.mk_bind ~build b v t)
    | TI.Let (v,t,u) ->
        let t = snf_term ~build ~subst:st.subst t in
        enter_snf_ ~build st v u (fun v u -> T.let_ ~build v t u)
    | TI.Match (t,l) ->
        let st_t = snf_ ~build {head=t; args=[]; subst=st.subst; } in
        (* see whether [st] matches some case *)
        begin match lookup_case_ ~build st_t l with
          | None ->
              (* just replace the head and evaluate each branch *)
              let l = ID.Map.map
                (fun (vars,rhs) ->
                  let vars' = Var.fresh_copies vars in
                  let subst' = Subst.add_list ~subst:st.subst vars
                    (List.map (T.var ~build) vars') in
                  let rhs' = snf_term ~build rhs ~subst:subst' in
                  vars',rhs'
                )
                l
              in
              { st with head=T.match_with ~build (term_of_state ~build st_t) l }
          | Some (rhs, subst) ->
              whnf_ ~build {st with head=rhs; subst; }
        end
    | TI.TyMeta _ -> assert false

  (* compute the SNF of this term in [subst] *)
  and snf_term
  : type t inv. build:(t,inv) build -> subst:t subst -> t -> t
  = fun ~build ~subst t ->
    term_of_state ~build (snf_ ~build {head=t; subst; args=[]})

  (* enter the scope of [v] and compute [snf t] *)
  and enter_snf_
  : type t inv.
      build:(t,inv) build -> t state -> t Var.t -> t ->
      (t Var.t -> t -> t) -> t state
  = fun ~build st v t f ->
    let v' = Var.fresh_copy v in
    let head = snf_term ~build t
      ~subst:(Subst.add ~subst:st.subst v (T.var ~build v')) in
    {st with head=f v' head; }
end

(* NOTE: when dependent types are added, substitution in types is needed *)

(** {6 Reduction State} *)

let whnf ~build t =
  let st = Full.whnf_ ~build {Full.subst=Subst.empty; head=t; args=[]} in
  Full.term_of_state ~build st

let snf ~build t =
  let st = Full.snf_ ~build {Full.subst=Subst.empty; head=t; args=[]} in
  Full.term_of_state ~build st


