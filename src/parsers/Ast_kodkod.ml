
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Trivial AST for Kodkod models} *)

type section =
  | S_outcome
  | S_instance
  | S_stats

type result =
  | Unsat
  | Trivially_unsat
  | Sat

type 'atom relation = {
  rel_name: string;
  rel_dom: 'atom list list;
}

let make_rel name dom =
  { rel_name=name; rel_dom=dom }

(* a model, as given by kodkod *)
type model = int relation list

