
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Transform a problem with multiple equations per defined Symbol into one with single equations} *)

module ID = NunID
module TI = NunTermInner
module Var = NunVar
module Stmt = NunStatement

type id = NunID.t
type 'a var = 'a Var.t

type ('a,'b) inv1 = <ty:'a; eqn:'b>
type 'a inv2 = <ty:'a; eqn:[`Single]>

module Make(T : TI.S) = struct
  module P = TI.Print(T)

  type term = T.t

  exception Error of string

  let spf = CCFormat.sprintf

  let () = Printexc.register_printer
    (function
      | Error msg ->
          Some ("elimination of multiple equations: " ^ msg)
      | _ -> None)

  let error_ msg = raise (Error msg)
  let errorf_ msg = NunUtils.exn_ksprintf msg ~f:error_

  (* decision tree for pattern matching *)
  type dtree =
    | Yield of term  (* rhs *)
    | Undefined
    | Decide of int * dtree ID.Map.t (* switch on the given sub-term *)

  (* list of terms [l] leads to [rhs]; add this to [dtree].
    @param i offset in the list of terms *)
  let rec dtree_add_ i l rhs dt =
    match l with
    | [] ->
        begin match dt with
        | Undefined -> Yield rhs
        | Yield rhs' ->
            errorf_
              "@[<hv2>ambiguous matching yielding@ `@[%a@]`@ or `@[%a@]`@]"
              P.print rhs P.print rhs'
        | Decide _ -> error_ "incompatible lengths of arguments"
        end
    | t :: l' ->
        begin match T.repr t, dt with
        | TI.Var v, _ -> assert false
        end

  let uniq_eqns
  : type a b.
    (term, term, (a,b) inv1) NunStatement.equations ->
    (term, term, a inv2) NunStatement.equations
  = function
  | Stmt.Eqn_single (vars,rhs) -> Stmt.Eqn_single (vars, rhs)
  | Stmt.Eqn_linear l ->
      assert false 

  let uniq_eqn_st st =
    let info = Stmt.info st in
    match Stmt.view st with
    | Stmt.Axiom (Stmt.Axiom_rec l) ->
        let l' = List.map 
          (fun def -> {def with Stmt.rec_eqns=uniq_eqns def.Stmt.rec_eqns})
          l
        in
        Stmt.axiom_rec ~info l'
    | Stmt.Axiom (Stmt.Axiom_spec l) -> Stmt.axiom_spec ~info l
    | Stmt.Axiom (Stmt.Axiom_std l) -> Stmt.axiom ~info l
    | Stmt.Decl (id,kind,ty) -> Stmt.mk_decl ~info id kind ty
    | Stmt.TyDef (k,ty) -> Stmt.mk_ty_def ~info k ty
    | Stmt.Goal g -> Stmt.goal ~info g

  let uniq_eqns_pb pb = NunProblem.map_statements ~f:uniq_eqn_st pb


  let pipe ~decode ~print =
    let on_encoded = if print
      then
        let module PPb = NunProblem.Print(P)(P) in
        [Format.printf "@[<v2>after uniq equations: %a@]@." PPb.print]
      else []
    and decode _ x = decode x in
    NunTransform.make1
      ~on_encoded
      ~name:"recursion_elim"
      ~encode:(fun p ->
        let p = uniq_eqns_pb p in
        p, ()
      ) ~decode
      ()
end


