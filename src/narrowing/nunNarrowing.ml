
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Lazy Evaluation} *)

module ID = NunID
module Var = NunVar
module Env = NunEvalEnv
module Subst = Var.Subst
module T = NunTermEval
module DBEnv = NunDBEnv
module VarSet = T.VarSet
module U = NunEvalUtils
module Const = NunEvalConst

type id = ID.t
type 'a var = 'a Var.t

(* TODO: env is not exactly going to fit:
  - we need some unification index for Prolog
  - we need to store the "spec" axioms for Prolog
*)

(** {2 State For Evaluation} *)

(** A single goal to solve: a toplevel term, with its environment *)
type goal = T.TermTop.t

type goals = {
  goals: goal list;
  goals_cost: int; (* cost for evaluating this branch so far *)
  goals_heuristic: int; (* estimated cost to completion *)
  goals_metas: VarSet.t;  (* metas blocking evaluation *)
}

(* heuristic: estimate the cost of solving [l] *)
let estimate_cost_ l = List.length l (* TODO *)

(** make a new {!goals}
    @param cost cost so far
    @param l the list of sub-goals to solve *)
let goals_make ~cost l =
  let goals_metas = List.fold_left
    (fun acc e ->
      match T.TermTop.blocked e with
        | None -> acc
        | Some v -> VarSet.add v acc)
    VarSet.empty l
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
    env: Env.t; (* environment containing the global definitions *)
    branches: GoalHeap.t; (* disjunction of conjunctions of goals *)
  }

  val make: unit -> t
  val find: t -> id -> T.ty Const.t option
  val find_exn: t -> id -> T.ty Const.t

  val add_branch: t -> goals -> t
  (** Add a new branch to explore *)

  val next_branch: t -> (t * goals) option
  (** Pop and return the next branch to explore *)
end = struct
  type t = {
    env: Env.t;
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
  - convert problem into goal+env (see {!T.OfPoly})
  - loop untime time limit/success/failure
  - return model of meta-variables
*)



