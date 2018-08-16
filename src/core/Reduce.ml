
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Reductions, including Beta Reduction} *)

module TI = TermInner
module Subst = Var.Subst

module type S = sig
  type term

  type subst = (term,term) Var.Subst.t

  val whnf : ?subst:subst -> term -> term
  (** Weak Head Normal Form *)

  val snf : ?subst:subst -> term -> term
  (** Strong Normal Form (reduce under functions) *)

  val app_whnf : ?subst:subst -> term -> term list -> term
  (** [app_whnf f l] applies [f] to [l], then computes the weak head normal form *)

  val eta_reduce : term -> term
  (** Eta-reduction at the root of the term.
      This replaces [λx. f x] with [f], if [f] does not contain [x] *)

  module Full : sig
    val whnf :
      ?subst:subst ->
      term ->
      term list ->
      (term * term list * subst * term Builtin.guard)
      (** [whnf f l] applies [f] to [l] and returns its WHNF, as a tuple
          [f', l', subst, guard] where
          [f l ---> subst ((f guard) l)] *)
  end
end

(* low level implementation *)
module Make(T : TI.FULL)
  : S with type term := T.t
= struct
  type subst = (T.t, T.t) Subst.t

  module State : sig
    (* head applied to args, in environment subst *)
    type t = private {
      head: T.t; (* invariant: not an App *)
      args: T.t list;
      subst: subst;
      guard: T.t Builtin.guard;
    }
    val make : guard:T.t Builtin.guard -> subst:subst -> T.t -> T.t list -> t
    val const : guard:T.t Builtin.guard -> subst:subst -> T.t -> t
    val set_head : t -> T.t -> t
    val map_guard : (T.t -> T.t) -> t -> t
    val to_term : ?rec_:bool -> t -> T.t
  end = struct
    type t = {
      head: T.t;
      args: T.t list;
      subst: subst;
      guard: T.t Builtin.guard;
    }

    let app_ a b = if b=[] then a else a @ b

    (* enforce the invariant about `head` not being an `App` *)
    let rec norm_st st = match T.repr st.head with
      | TI.App (f, l) -> norm_st {st with head=f; args=app_ l st.args}
      | TI.Builtin (`Guard (t,g)) ->
        norm_st {st with head=t; guard=Builtin.merge_guard g st.guard}
      | _ -> st

    (* build a state and enforce invariant *)
    let make ~guard ~subst f l =
      norm_st {head=f; args=l; subst; guard; }

    let const ~guard ~subst t = make ~guard ~subst t []

    let set_head st t = norm_st {st with head=t}

    let map_guard f st = {st with guard=Builtin.map_guard f st.guard}

    (* convert a state back to a term *)
    let to_term ?rec_ st =
      let t = T.guard (T.app st.head st.args) st.guard in
      T.eval ?rec_ ~subst:st.subst t
  end

  module Full = struct
    open State

    type bool_ =
      | BTrue
      | BFalse
      | BPartial of T.t

    let as_bool_ t = match T.repr t with
      | TI.Builtin `True -> BTrue
      | TI.Builtin `False -> BFalse
      | _ -> BPartial t

    let rec eval_and_l ~eval ~subst ~acc l = match l with
      | [] -> T.and_ (List.rev acc)
      | t :: l' ->
        match eval ~subst t |> as_bool_ with
          | BTrue -> eval_and_l ~eval ~subst ~acc l'
          | BFalse -> T.false_
          | BPartial t' -> eval_and_l ~eval ~subst ~acc:(t'::acc) l'

    let rec eval_or_l ~eval ~subst ~acc l = match l with
      | [] -> T.or_ (List.rev acc)
      | t :: l' ->
        match eval ~subst t |> as_bool_ with
          | BTrue -> T.true_
          | BFalse -> eval_or_l ~eval ~subst ~acc l'
          | BPartial t' -> eval_or_l ~eval ~subst ~acc:(t'::acc) l'

    (* Evaluate boolean operators [app_builtin b].
       Subterms are evaluated with [eval] *)
    let eval_bool_builtin ~eval ~subst (b : _ Builtin.t) =
      match b with
        | `True -> T.true_
        | `False -> T.false_
        | `Unparsable _ | `Card_at_least _ | `Undefined_self _
        | `Undefined_atom _ | `Guard _ ->
          T.builtin b (* undefined term doesn't evaluate *)
        | `Ite (_,_,_) | `DataSelect _ | `DataTest _ ->
          invalid_arg "not boolean operators"
        | `Eq (a,b) ->
          let a = eval ~subst a in
          let b = eval ~subst b in
          begin match as_bool_ a, as_bool_ b with
            | BTrue, BTrue
            | BFalse, BFalse -> T.true_
            | BTrue, BFalse
            | BFalse, BTrue -> T.false_
            | BPartial _, _
            | _, BPartial _ ->
              begin match T.repr a, T.repr b with
                | TI.Const id_a, TI.Const id_b
                  when ID.is_distinct id_a && ID.is_distinct id_b ->
                  (* equality is always decidable for those constants *)
                  if ID.equal id_a id_b then T.true_ else T.false_
                | _ ->
                  (* can only answer positively. *)
                  if T.equal_with ~subst a b
                  then T.true_
                  else T.eq a b
                  (* TODO: if [a] and [b] fully evaluated, return [false]?*)
              end
          end
        | `And l -> eval_and_l ~eval ~subst ~acc:[] l
        | `Or l -> eval_or_l ~eval ~subst ~acc:[] l
        | `Imply (a,b) ->
          (* truth table *)
          let a' = eval ~subst a in
          let b' = eval ~subst b in
          begin match as_bool_ a', as_bool_ b' with
            | _, BTrue
            | BFalse, _ -> T.true_
            | BTrue, BFalse -> T.false_
            | BPartial _, _
            | _, BPartial _ -> T.imply a' b'
          end
        | `Not f' ->
          begin match eval ~subst f' |> as_bool_ with
            | BTrue -> T.false_
            | BFalse -> T.true_
            | BPartial t -> T.not_ t
          end

    (* evaluate [b] using [eval]. *)
    let eval_app_builtin ~eval ~subst ~guard (b:T.t Builtin.t) args =
      (* auxiliary function to evaluate subterms. No guard initially. *)
      let eval_term ~subst t =
        State.make ~guard:Builtin.empty_guard ~subst t []
        |> eval
        |> State.to_term ~rec_:true
      in
      match b with
        | `True | `False ->
          assert (args=[]);
          State.const ~guard ~subst (T.builtin b)(* normal form *)
        | `And _ | `Imply _ | `Not _ | `Or _ | `Eq _ ->
          assert (args = []);
          begin match
              eval_bool_builtin ~eval:eval_term ~subst b
              |> as_bool_
            with
              | BTrue -> State.const ~guard ~subst T.true_
              | BFalse -> State.const ~guard ~subst T.false_
              | BPartial t -> State.const ~guard ~subst t
          end
        | `Ite (a,b,c) ->
          (* special case: ite can reduce further if [a] reduces to
             a boolean, because then branches can be functions *)
          begin match
              eval_term ~subst a |> as_bool_
            with
              | BTrue -> eval (State.make ~guard ~subst b args)
              | BFalse -> eval (State.make ~guard ~subst c args)
              | BPartial a' -> State.make ~guard ~subst (T.ite a' b c) args
          end
        | `DataTest _ ->
          Utils.not_implemented "evaluation of DataTest"
        | `DataSelect (_,_) ->
          Utils.not_implemented "evaluation of DataSelect"
        | `Unparsable _
        | `Undefined_self _
        | `Undefined_atom _
        | `Card_at_least _
        | `Guard _ ->
          (* no evaluation *)
          State.make ~guard ~subst (T.builtin b) args

    (* see whether [st] matches a case in [m] *)
    let lookup_case_ st (m:_ TI.cases) def = match T.repr st.head with
      | TI.Const id ->
        begin
          try
            let _tys, vars, rhs = ID.Map.find id m in
            let n = List.length vars in
            (* it matches! arity should match too, otherwise the
               term is ill-typed *)
            if n>List.length st.args then failwith "partial application of match";
            let matched_args, other_args = CCList.take_drop n st.args in
            let subst = Subst.add_list ~subst:st.subst vars matched_args in
            Some (rhs, other_args, subst)
          with Not_found ->
            begin match def with
              | Some (rhs, m) when ID.Map.mem id m ->
                let arity = ID.Map.find id m in
                if arity>List.length st.args then failwith "partial application of match";
                (* drop [arity] arguments *)
                let _, other_args = CCList.take_drop arity st.args in
                Some (rhs, other_args, st.subst)
              | _ -> None
            end
        end
      | _ -> None

    (* reduce until the head is not a function *)
    let rec whnf_ st =
      let head = st.head in
      match T.repr head with
        | TI.Const _ -> st
        | TI.Builtin (`False | `True) -> st
        | TI.Builtin b ->
          eval_app_builtin ~guard:st.guard ~eval:whnf_ ~subst:st.subst b st.args
        | TI.Var v ->
          (* dereference, if any *)
          begin match Subst.find ~subst:st.subst v with
            | None -> st
            | Some t -> whnf_ (State.set_head st t)
          end
        | TI.App _ -> assert false (* broken invariant *)
        | TI.Bind (Binder.Fun, v, body) ->
          begin match st.args with
            | [] -> st
            | a :: args' ->
              (* beta-redex *)
              let subst = Subst.add ~subst:st.subst v a in
              whnf_ (State.make ~guard:st.guard ~subst body args')
          end
        | TI.Match (t, l, def) ->
          let st_t = whnf_ (State.const ~guard:Builtin.empty_guard ~subst:st.subst t) in
          (* see whether [st] matches some case *)
          begin match lookup_case_ st_t l def with
            | None ->
              (* just replace the head *)
              State.set_head st (T.match_with (State.to_term st_t) l ~def)
            | Some (rhs, args, subst) ->
              whnf_ (State.make ~guard:st.guard ~subst rhs args)
          end
        | TI.Bind (Binder.TyForall, _, _) -> assert false
        | TI.Bind ((Binder.Forall | Binder.Exists | Binder.Mu), _, _) -> st
        | TI.Let _
        | TI.TyBuiltin _
        | TI.TyArrow _ -> st
        | TI.TyMeta _ -> assert false

    and whnf ?(subst=Subst.empty) t args =
      let {head; args; subst; guard} =
        whnf_ (State.make ~guard:Builtin.empty_guard ~subst t args)
      in
      head, args, subst, guard

    (* strong normal form *)
    let rec snf_ st =
      (* first, head reduction *)
      let st = whnf_ st in
      let st = State.map_guard (snf_term ~subst:st.subst) st in
      (* then, reduce subterms *)
      match T.repr st.head with
        | TI.TyBuiltin _
        | TI.Const _ -> st
        | TI.Builtin (`Guard _) -> assert false
        | TI.Builtin b ->
          eval_app_builtin ~guard:st.guard ~eval:snf_ ~subst:st.subst b st.args
        | TI.Bind (Binder.TyForall,_,_) -> st
        | TI.TyArrow (_,_) ->
          st (* NOTE: depend types might require beta-reduction in types *)
        | TI.Var v ->
          assert (not (Subst.mem ~subst:st.subst v));
          st
        | TI.App (_,_) -> assert false  (* not WHNF *)
        | TI.Bind (Binder.Fun, v, body) ->
          assert (st.args = []);
          enter_snf_ st v body (fun v body -> T.fun_ v body)
        | TI.Bind (b, v,t) ->
          enter_snf_ st v t (fun v t -> T.mk_bind b v t)
        | TI.Let (v,t,u) ->
          let t = snf_term ~subst:st.subst t in
          enter_snf_ st v u (fun v u -> T.let_ v t u)
        | TI.Match (t,l,def) ->
          let st_t = snf_ (State.const ~guard:Builtin.empty_guard ~subst:st.subst t) in
          (* see whether [st] matches some case *)
          begin match lookup_case_ st_t l def with
            | None ->
              (* just replace the head and evaluate each branch *)
              let l = ID.Map.map
                  (fun (tys,vars,rhs) ->
                     let subst', vars' = Utils.fold_map T.rename_var st.subst vars in
                     let rhs' = snf_term rhs ~subst:subst' in
                     tys,vars',rhs')
                  l
              in
              State.set_head st (T.match_with (State.to_term st_t) l ~def)
            | Some (rhs, args, subst) ->
              whnf_ (State.make ~guard:st.guard ~subst rhs args)
          end
        | TI.TyMeta _ -> assert false

    (* compute the SNF of this term in [subst] *)
    and snf_term ~subst t =
      State.to_term ~rec_:true
        (snf_ (State.const ~guard:Builtin.empty_guard ~subst t))

    (* enter the scope of [v] and compute [snf t] *)
    and enter_snf_ st v t f =
      let v' = Var.fresh_copy v in
      let head = snf_term t
          ~subst:(Subst.add ~subst:st.subst v (T.var v')) in
      State.set_head st (f v' head)
  end

  (* NOTE: when dependent types are added, substitution in types is needed *)

  (** {6 Reduction State} *)

  let whnf ?(subst=Subst.empty) t =
    let st = Full.whnf_ (State.const ~guard:Builtin.empty_guard ~subst t) in
    State.to_term st

  let app_whnf ?(subst=Subst.empty) f l =
    let st = Full.whnf_ (State.make ~guard:Builtin.empty_guard ~subst f l) in
    State.to_term st

  let snf ?(subst=Subst.empty) t =
    let st = Full.snf_ (State.const ~guard:Builtin.empty_guard ~subst t) in
    State.to_term ~rec_:true st

  (* if [t = f x1...xn var], this returns [Some (f x1...xn)] *)
  let as_app_to_ ~var:v t = match T.repr t with
    | TI.App (f, l) ->
      begin match List.rev l with
        | last :: l' ->
          (* sequence of free variables in [f (rev l')] *)
          let fvars =
            Sequence.of_list (f :: l')
            |> Sequence.flat_map (T.to_seq_free_vars ?bound:None)
          in
          begin match T.repr last with
            | TI.Var v' when Var.equal v v'
                          && not (Sequence.mem ~eq:Var.equal v fvars)  ->
              (* so, [t = f (rev l' @ [v])], and neither [f] nor [l']
                 contain [v], so we can reduce to [f (rev l')] *)
              Some (T.app f (List.rev l'))
            | _ -> None
          end
        | [] -> assert false
      end
    | _ -> None

  let rec eta_reduce t = match T.repr t with
    | TI.Bind (Binder.Fun, v, body) ->
      begin match as_app_to_ ~var:v body with
        | None -> t
        | Some t' -> eta_reduce t'
      end
    | _ -> t
end

(*$inject
  module T = Term_random.T
  module Red = T.Red
*)

(* distinct IDs *)
(*$R
  let a = ID.make_full ~needs_at:false ~distinct:true "a" |> T.const in
  let b = ID.make_full ~needs_at:false ~distinct:true "b" |> T.const in
  let x = Var.make ~name:"x" ~ty:T.ty_unitype in
  let fun_id = T.fun_ x (T.var x) in
  assert_equal ~cmp:T.equal ~printer:T.to_string T.false_ (Red.whnf (T.eq a b));
  assert_equal ~cmp:T.equal ~printer:T.to_string T.false_
    (Red.whnf (T.or_ [T.eq a b; T.not_ (T.eq (T.app fun_id [a]) a)]));
*)

(* idempotence of WHNF *)
(*$QR
  Term_random.arbitrary
    (fun t ->
      let t = Red.whnf t in
      let t' = Red.whnf t in
      if T.equal t t' then true
      else (
        Q.Test.fail_reportf "term `%a`,@ whnf: `%a`" T.pp t T.pp t';
      ))
*)

(* WHNF/SNF on types is identity *)
(*$Q
  Term_random.arbitrary_ty (fun ty -> T.equal ty (Red.whnf ty))
  Term_random.arbitrary_ty (fun ty -> T.equal ty (Red.snf ty))
*)


(* idempotence of SNF *)
(*$QR
  Term_random.arbitrary
    (fun t ->
      let t_norm = Red.snf t in
      let t_norm2 = Red.snf t_norm in
      if T.equal t_norm t_norm2 then true
      else (
        Q.Test.fail_reportf "snf=`%a`@ snf2=`%a`" T.pp t_norm T.pp t_norm2
      ))
*)



