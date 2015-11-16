
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Lazy Evaluation} *)

module ID = NunID
module Var = NunVar
module Env = NunEnv
module Subst = Var.Subst

module ANF = NunANF

type id = ID.t
type 'a var = 'a Var.t

type subst = (ANF.value, ANF.value) Subst.t

(* TODO: env is not exactly going to fit:
  - we need some unification index for Prolog
  - we need to store the "spec" axioms for Prolog
  - we need very efficient access to definition of functions
  - merge LocalEnv and the new env would be nice, or at least pair
    them in one structure (fixed part=constructors/funs, local part=let/beta)
*)
type env = ANF.env

type info = (ANF.expr, ANF.value, [`Nested]) Env.info

module VVarSet = Var.Set(struct type t = ANF.value end)

(** {2 Local Environment} *)
module LocalEnv = struct
  type entry =
    | Def of ANF.t_var * ANF.value * ANF.ty
    | Decl of ANF.t_var * ANF.ty

  type t = entry ID.PerTbl.t

  let create() = ID.PerTbl.create 16
  let find_exn ~env v = ID.PerTbl.find env (Var.id v)
  let find ~env v = try Some (ID.PerTbl.find env (Var.id v)) with Not_found -> None
  let def ~env v ~ty t = ID.PerTbl.add env (Var.id v) (Def (v, t, ty))
  let decl ~env v ~ty = ID.PerTbl.add env (Var.id v) (Decl (v,ty))
end

(** {2 State For Evaluation} *)

(** A single goal to solve: expression paired with its environment *)
type goal = {
  goal_expr: ANF.expr_top;
  goal_env: LocalEnv.t; (* private local environment for the expression *)
}

type goals = {
  goals: goal list;
  goals_cost: int; (* cost for evaluating this branch so far *)
  goals_heuristic: int; (* estimated cost to completion *)
  goals_metas: VVarSet.t;  (* metas blocking evaluation *)
}

(* heuristic: estimate the cost of solving [l] *)
let estimate_cost_ l = List.length l (* TODO *)

(** make a new {!goals}
    @param cost cost so far
    @param l the list of sub-goals to solve *)
let goals_make ~cost l =
  let goals_metas = List.fold_left
    (fun acc e -> match e.goal_expr.ANF.blocked with
      | None -> acc
      | Some v -> VVarSet.add v acc)
    VVarSet.empty l
  in
  let goals_heuristic = estimate_cost_ l in
  { goals=l; goals_metas; goals_cost=cost; goals_heuristic; }

let goals_total_cost g = g.goals_cost + g.goals_heuristic

module GoalHeap = CCHeap.Make(struct
  type t = goals
  let leq g1 g2 = goals_total_cost g1 <= goals_total_cost g2
end)

(** Evaluation state, with several expressions to be reduced in parallel *)
module State : sig
  type t = private {
    env: env; (* environment containing the global definitions *)
    branches: GoalHeap.t; (* disjunction of conjunctions of goals *)
  }

  val make: unit -> t
  val find: t -> id -> info option
  val find_exn: t -> id -> info

  val add_branch: t -> goals -> t
  (** Add a new branch to explore *)

  val next_branch: t -> (t * goals) option
  (** Pop and return the next branch to explore *)
end = struct
  type t = {
    env: env;
    branches: GoalHeap.t; (* disjunction of conjunctions of goals *)
  }

  let make () = {
    env=Env.create();
    branches=GoalHeap.empty;
  }
  let find t id = Env.find ~env:t.env id
  let find_exn t id = Env.find_exn ~env:t.env id
  let add_branch st b = {st with branches=GoalHeap.add st.branches b}
  let next_branch st = match GoalHeap.take st.branches with
    | None -> None
    | Some (h', x) -> Some ({st with branches=h'}, x)
end

(* TODO: evaluation function, type goal -> goal list * cost *)
(* TODO: refinement function, type goals -> goals list
  - pick a meta-variable to refine
  - for each constructor, introduce new metas, substitute, and evaluate
  - keep the branches that did not fail *)
(* TODO: main loop:
  - pick next [goals]
  - check for success/failure
  - refine a variable
  - loop *)
(* TODO: main function (closing pipe):
  - convert problem into goal+env (see {!ANF.OfPoly})
  - loop untime time limit/success/failure
  - return model of meta-variables
*)



