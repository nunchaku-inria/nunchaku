
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Reductions, including Beta Reduction} *)

module TI = TermInner
module Subst = Var.Subst

(* low level implementation *)
module Make(T : TI.S) = struct
  module U = TI.Util(T)

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
      let t = U.guard (U.app st.head st.args) st.guard in
      U.eval ?rec_ ~subst:st.subst t
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
      | [] -> U.and_ (List.rev acc)
      | t :: l' ->
        match eval ~subst t |> as_bool_ with
          | BTrue -> eval_and_l ~eval ~subst ~acc l'
          | BFalse -> U.false_
          | BPartial t' -> eval_and_l ~eval ~subst ~acc:(t'::acc) l'

    let rec eval_or_l ~eval ~subst ~acc l = match l with
      | [] -> U.or_ (List.rev acc)
      | t :: l' ->
        match eval ~subst t |> as_bool_ with
          | BTrue -> U.true_
          | BFalse -> eval_or_l ~eval ~subst ~acc l'
          | BPartial t' -> eval_or_l ~eval ~subst ~acc:(t'::acc) l'

    (* Evaluate boolean operators [app_builtin b].
       Subterms are evaluated with [eval] *)
    let eval_bool_builtin ~eval ~subst (b : _ Builtin.t) =
      match b with
        | `True -> U.true_
        | `False -> U.false_
        | `Unparsable _ | `Undefined_self _ | `Undefined_atom _ | `Guard _ ->
          U.builtin b (* undefined term doesn't evaluate *)
        | `Ite (_,_,_) | `DataSelect _ | `DataTest _ ->
          invalid_arg "not boolean operators"
        | `Eq (a,b) ->
          let a = eval ~subst a in
          let b = eval ~subst b in
          (* TODO: if [a] and [b] fully evaluated, return False? *)
          begin match as_bool_ a, as_bool_ b with
            | BTrue, BTrue
            | BFalse, BFalse -> U.true_
            | BTrue, BFalse
            | BFalse, BTrue -> U.false_
            | BPartial _, _
            | _, BPartial _ ->
              if U.equal_with ~subst a b
              then U.true_
              else U.eq a b
          end
        | `And l -> eval_and_l ~eval ~subst ~acc:[] l
        | `Or l -> eval_or_l ~eval ~subst ~acc:[] l
        | `Imply (a,b) ->
          (* truth table *)
          let a' = eval ~subst a in
          let b' = eval ~subst b in
          begin match as_bool_ a', as_bool_ b' with
            | _, BTrue
            | BFalse, _ -> U.true_
            | BTrue, BFalse -> U.false_
            | BPartial _, _
            | _, BPartial _ -> U.imply a' b'
          end
        | `Not f' ->
          begin match eval ~subst f' |> as_bool_ with
            | BTrue -> U.false_
            | BFalse -> U.true_
            | BPartial t -> U.not_ t
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
          State.const ~guard ~subst (U.builtin b)(* normal form *)
        | `And _ | `Imply _ | `Not _ | `Or _ | `Eq _ ->
          assert (args = []);
          begin match
              eval_bool_builtin ~eval:eval_term ~subst b
              |> as_bool_
            with
              | BTrue -> State.const ~guard ~subst U.true_
              | BFalse -> State.const ~guard ~subst U.false_
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
              | BPartial a' -> State.make ~guard ~subst (U.ite a' b c) args
          end
        | `DataTest _ ->
          Utils.not_implemented "evaluation of DataTest"
        | `DataSelect (_,_) ->
          Utils.not_implemented "evaluation of DataSelect"
        | `Unparsable _
        | `Undefined_self _
        | `Undefined_atom _
        | `Guard _ ->
          (* no evaluation *)
          State.make ~guard ~subst (U.builtin b) args

    (* see whether [st] matches a case in [m] *)
    let lookup_case_ st m def = match T.repr st.head with
      | TI.Const id ->
        begin
          try
            let vars, rhs = ID.Map.find id m in
            let n = List.length vars in
            (* it matches! arity should match too, otherwise the
               term is ill-typed *)
            if n>List.length st.args then failwith "partial application of match";
            let matched_args, other_args = CCList.take_drop n st.args in
            let subst = Subst.add_list ~subst:st.subst vars matched_args in
            Some (rhs, other_args, subst)
          with Not_found ->
            begin match def with
              | TI.Default_some (rhs, m) when ID.Map.mem id m ->
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
              State.set_head st (U.match_with (State.to_term st_t) l ~def)
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
          enter_snf_ st v body (fun v body -> U.fun_ v body)
        | TI.Bind (b, v,t) ->
          enter_snf_ st v t (fun v t -> U.mk_bind b v t)
        | TI.Let (v,t,u) ->
          let t = snf_term ~subst:st.subst t in
          enter_snf_ st v u (fun v u -> U.let_ v t u)
        | TI.Match (t,l,def) ->
          let st_t = snf_ (State.const ~guard:Builtin.empty_guard ~subst:st.subst t) in
          (* see whether [st] matches some case *)
          begin match lookup_case_ st_t l def with
            | None ->
              (* just replace the head and evaluate each branch *)
              let l = ID.Map.map
                  (fun (vars,rhs) ->
                     let subst', vars' = Utils.fold_map U.rename_var st.subst vars in
                     let rhs' = snf_term rhs ~subst:subst' in
                     vars',rhs')
                  l
              in
              State.set_head st (U.match_with (State.to_term st_t) l ~def)
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
          ~subst:(Subst.add ~subst:st.subst v (U.var v')) in
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
            |> Sequence.flat_map (U.to_seq_free_vars ?bound:None)
          in
          begin match T.repr last with
            | TI.Var v' when Var.equal v v'
                          && not (Sequence.mem ~eq:Var.equal v fvars)  ->
              (* so, [t = f (rev l' @ [v])], and neither [f] nor [l']
                 contain [v], so we can reduce to [f (rev l')] *)
              Some (U.app f (List.rev l'))
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
  module U = TermInner.Util(T)
  module Red = Make(T)
  module P = TermInner.Print(T)
*)

(* idempotence of WHNF *)
(*$QR
  (Q.map_keep_input ~print:P.to_string Red.whnf Term_random.arbitrary)
    (fun (t, t') -> U.equal t' (Red.whnf t'))
*)

(* WHNF/SNF type is identity *)
(*$Q
  Term_random.arbitrary_ty (fun ty -> U.equal ty (Red.whnf ty))
  Term_random.arbitrary_ty (fun ty -> U.equal ty (Red.snf ty))
*)


(* idempotence of SNF *)
(*$QR
  (Q.map_keep_input ~print:P.to_string Red.snf Term_random.arbitrary)
    (fun (t, t_norm) ->
      U.equal t_norm (Red.snf t_norm))
*)



