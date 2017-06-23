
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Eliminate Quantifiers} *)

open Nunchaku_core

module TI = TermInner
module Stmt = Statement
module T = TermInner.Default
module U = T.U
module P = T.P
module Pol = Polarity

let name = "elim_quant"

let section = Utils.Section.make name

type term = T.t
type ty = T.t

(** {2 Prelude} *)

type to_elim =
  | Elim_quant_data (* remove quantifiers on datatypes *)
  | Elim_quant_fun (* remove quantifiers on functions *)
  | Elim_eq_fun (* remove equality on functions *)

type mode = to_elim list

let pp_to_elim out = function
  | Elim_quant_data -> CCFormat.string out "elim_quant_data"
  | Elim_quant_fun -> CCFormat.string out "elim_quant_fun"
  | Elim_eq_fun -> CCFormat.string out "elim_eq_fun"

let pp_mode = CCFormat.Dump.list pp_to_elim

module Sk = Skolem.Make(struct type t = ty end)

type state = {
  env: (term, ty) Env.t;
  sk: Sk.state;
  mode: mode;
  mutable unsat_means_unknown: bool;
}

type decode_state = unit

let create_state ~env ~mode () = {
  env;
  mode;
  sk=Sk.create ();
  unsat_means_unknown=false;
}

let error msg = failwith ("in " ^ name ^ ": " ^ msg)
let errorf msg = Utils.exn_ksprintf ~f:error msg

(** {2 Encoding} *)

let must_elim_quant_data st = List.mem Elim_quant_data st.mode
let must_elim_quant_fun st = List.mem Elim_quant_fun st.mode
let must_elim_eq_fun st = List.mem Elim_eq_fun st.mode

(* is this a type for which all quantifiers must be removed? *)
let must_elim_quant_on st ty = match T.repr ty with
  | TI.Const id ->
    Env.is_data (Env.find_exn ~env:st.env id) && must_elim_quant_data st
  | TI.TyArrow _ -> must_elim_quant_fun st
  | _ -> false

let must_elim_eq_on st ty = match T.repr ty with
  | TI.TyArrow _ -> must_elim_eq_fun st
  | _ -> false

type local_env = {
  vars: ty Var.t list; (* bound variables *)
  subst: (ty, term) Var.Subst.t; (* substitutions *)
}

let lenv_empty = { vars=[]; subst=Var.Subst.empty }

let bind_var (lenv:local_env) v =
  let subst, v' = U.rename_var lenv.subst v in
  { subst; vars=[v'] }, v'

let ty_infer state (t:term): ty =
  U.ty_exn ~env:state.env t

(* We remove positive-existential variables that have a type
   matching [mode] (i.e. a datatype, or a function type, in general).

   Consider [goal forall x:bool. P[x] && exists y:(a -> b). Q[x,y] ].
   We keep the [forall] because its type is simple, but we introduce
   a new symbol [f: bool -> a -> b] at toplevel.

   The result should look like:
   [val f : bool -> a -> b.
    goal forall x:bool. P[x] && Q[x, f x]]
*)
let encode_term (state:state) lenv (pol:Pol.t) (t:term) : term =
  let rec aux (lenv:local_env) pol t = match T.repr t with
    | TI.Var v ->
      Var.Subst.find_exn ~subst:lenv.subst v
    | TI.Bind ((Binder.Forall | Binder.Exists) as q, v, body)
      when must_elim_quant_on state (Var.ty v) ->
      (* quantifier over an infinite (co)data, must approximate
           depending on the polarity *)
      begin match U.approx_infinite_quant_pol_binder q pol with
        | `Unsat_means_unknown res ->
          state.unsat_means_unknown <- true;
          Utils.debugf ~section 3
            "@[<2>encode `@[%a@]`@ as `%a` in pol %a,@ \
             quantifying over infinite encoded type `@[%a@]`@]"
            (fun k->k P.pp t P.pp res Pol.pp pol P.pp (Var.ty v));
          res
        | `Keep ->
          (* make a fresh undefined constant, parametrized over all
             the surrounding variables *)
          let vars = lenv.vars in
          let skolem_id, _, _ =
            Sk.skolemize state.sk ~prefix:(Var.name v) ~ty_ret:(Var.ty v) ~vars (fun ty->ty)
          in
          (* now apply the new constant to [vars] and [body] *)
          let skolem = U.app (U.const skolem_id) (List.map U.var vars) in
          (* convert [body] and replace [v] with [skolem] in it *)
          let lenv =
            {lenv with subst=Var.Subst.add ~subst:lenv.subst v skolem}
          in
          aux lenv pol body
      end
    | TI.Builtin (`Eq (a,b)) ->
      let ty = ty_infer state a in
      if must_elim_quant_on state ty then
        (* see whether we can keep this equality: if it's between objects
           in an infinite type (e.g. functions) we should kill it *)
        begin match U.approx_infinite_quant_pol `Eq pol with
          | `Unsat_means_unknown res ->
            state.unsat_means_unknown <- true;
            Utils.debugf ~section 3
              "@[<2>encode `@[%a@]`@ as `%a` in pol %a,@ \
               quantifying over infinite encoded type `@[%a@]`@]"
              (fun k->k P.pp t P.pp res Pol.pp pol P.pp ty);
            res
          | `Keep ->
            (* make fresh undefined constant(s) and apply to them *)
            let _, ty_args, _ = U.ty_unfold ty in
            (* create new constants [x1,...,xn] of type [ty_args], then state
               [(a x1..xn)=(b x1..xn)] as we must be in negative polarity *)
            let args =
              List.mapi
                (fun i ty ->
                   let vars = lenv.vars in
                   let skolem_id, _, _ =
                     Sk.skolemize state.sk
                       ~prefix:(CCFormat.sprintf "eq_arg_%d" i)
                       ~ty_ret:ty ~vars (fun ty->ty)
                   in
                   (* now apply the new constant to [vars] and [body] *)
                   let skolem = U.app (U.const skolem_id) (List.map U.var vars) in
                   skolem)
                ty_args
            in
            (* return [a] and [b], and apply them to [args] *)
            let a = aux lenv Pol.NoPol a in
            let b = aux lenv Pol.NoPol b in
            U.eq (U.app a args) (U.app b args)
        end
      else (
        aux_map lenv pol t
      )
    | _ ->
      aux_map lenv pol t
  (* default behavior: map through *)
  and aux_map lenv pol t =
    U.map_pol lenv pol t ~bind:bind_var ~f:aux
  in
  aux lenv pol t

let pop_new_stmts state =
  let l = Sk.pop_new_decls state.sk in
  List.map
    (fun (id,ty) ->
       Stmt.decl
         ~info:Stmt.info_default ~attrs:[] id ty)
    l

let encode_stmt state (st:(_,_)Stmt.t) : (term, term) Stmt.t list =
  let st' =
    Stmt.map_bind lenv_empty st ~bind:bind_var
      ~ty:(fun _ ty->ty) ~term:(encode_term state)
  in
  pop_new_stmts state @ [st']

let encode_pb ~mode pb : (term, term) Problem.t * decode_state =
  let env = Problem.env pb in
  let state = create_state ~env ~mode () in
  let new_stmts =
    CCVector.flat_map_list (encode_stmt state) (Problem.statements pb)
  in
  let meta = ProblemMetadata.add_unsat_means_unknown
      state.unsat_means_unknown
      (Problem.metadata pb)
  in
  Problem.make ~meta new_stmts, ()

(** {2 Decoding} *)

(* trivial *)
let decode_model () m = m

(** {2 Plumbing} *)

let pipe ~print ~check ~mode =
  let on_encoded =
    Utils.singleton_if print () ~f:(fun () ->
      let module Ppb = Problem.Print(P)(P) in
      Format.printf "@[<v2>@{<Yellow>after %s@}:@ %a@]@." name Ppb.pp)
    @
      Utils.singleton_if check () ~f:(fun () ->
        let module C = TypeCheck.Make(T) in
        C.empty () |> C.check_problem)
  in
  let decode st = Problem.Res.map_m ~f:(decode_model st) in
  Transform.make
    ~name
    ~input_spec:Transform.Features.(of_list [Ty, Mono])
    ~map_spec:(fun s->s)
    ~on_encoded
    ~encode:(encode_pb ~mode)
    ~decode
    ()

