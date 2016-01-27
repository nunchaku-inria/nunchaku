
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Recursive Traversal of AST} *)

module Stmt = Statement
module Loc = Location

module type ARG = sig
  type t
  val equal : t -> t -> bool
  val hash : t -> int

  val print : t CCFormat.printer
  val section : Utils.Section.t
  val fail : ('a, Format.formatter, unit, 'b) format4 -> 'a
end

type conf = {
  direct_tydef: bool;
  direct_spec: bool;
  direct_mutual_types: bool;
  direct_copy: bool;
}

(* union-find list *)
module UF_list = struct
  type 'a t = {
    mutable root: 'a t;
    mutable res: 'a list;
  }

  let make res =
    let rec l = { root=l; res; } in
    l

  let rec find x =
    if x.root == x then x
    else (
      let root = find x.root in
      x.root <- root; (* path compression *)
      root
    )

  let find_res x = (find x).res

  let same l1 l2 = find l1 == find l2

  (* append [l] in [x] *)
  let append l x =
    let x = find x in
    x.res <- List.rev_append l x.res

  let merge a b =
    let a = find a
    and b = find b in
    if a != b then (
      (* merge b into a *)
      a.res <- List.rev_append b.res a.res;
      b.root <- a;
    )
end

module Make(T : TermInner.S)(Arg : ARG) = struct
  module P = TermInner.Print(T)
  module PStmt = Stmt.Print(P)(P)

  type term = T.t

  let section = Arg.section

  module IDArgTbl = CCHashtbl.Make(struct
    type t = ID.t * Arg.t
    let equal (i1,a1)(i2,a2) = ID.equal i1 i2 && Arg.equal a1 a2
    let hash (i,a) = Hashtbl.hash (ID.hash i, Arg.hash a)
  end)

  (* a stack frame for building mutually recursive blocks *)
  type 'a stack_frame = {
    sf_id: ID.t;
    sf_def: 'a;
    mutable sf_is_root: bool;
  }

  class virtual ['inv1, 'inv2, 'c] traverse ~conf ?(size=64) ?(depth_limit=256) () = object (self)
    (* access definitions/declarations by ID *)
    val mutable env : (term, term, 'inv1) Env.t = Env.create()

    (* did we reach the maximal depth? *)
    val mutable depth_reached: bool = false

    (* resulting statements *)
    val output: (term, term, 'inv2) Stmt.t CCVector.vector = CCVector.create()

    (* symbols already declared *)
    val declared : unit IDArgTbl.t = IDArgTbl.create size

    (* pairs (id, arg) that are either:
       - being processed (with their stack frame)
       - done being processed *)
    val processed
    : [>`Done | `In of 'c stack_frame] IDArgTbl.t
    = IDArgTbl.create size

    (* stack of blocks being traversed *)
    val mutable stack : 'c stack_frame list = []

    method private check_depth d =
      if d>depth_limit && not depth_reached then (
        Utils.debugf ~section 1 "caution: depth limit reached" (fun k -> k);
        depth_reached <- true;
      )

    method private push x = stack <- x :: stack

    method private pop = match stack with
      | [] -> assert false
      | _ :: l -> stack <- l

    (* are we already done with this (ID, value)? *)
    method status: ID.t -> Arg.t -> [`Done | `In of 'c stack_frame | `New]
      = fun id arg ->
        try IDArgTbl.find processed (id, arg)
        with Not_found -> `New

    method has_processed id arg = self#status id arg = `Done

    (* have we declared this non-defined (id,arg) (axiom, opaque declarations…) *)
    method has_declared: ID.t -> Arg.t -> bool
      = fun id arg -> IDArgTbl.mem declared (id, arg)

    (* processing of (id,arg) is finished *)
    method done_processing : ID.t -> Arg.t -> unit
      = fun id arg ->
        Utils.debugf ~section 4 "done processing `%a` (%a)" (fun k->k ID.print id Arg.print arg);
        IDArgTbl.replace processed (id, arg) `Done

    (* signal we are currently processing this (id,arg) in the given frame *)
    method in_processing : ID.t -> Arg.t -> 'c stack_frame -> unit
      = fun id arg f -> IDArgTbl.replace processed (id, arg) (`In f)

    method done_declaring : ID.t -> Arg.t -> unit
      = fun id arg -> IDArgTbl.replace declared (id, arg) ()

    method push_res : (term, term, 'inv2) Stmt.t -> unit
      = fun stmt -> CCVector.push output stmt

    method reached_depth_limit = depth_reached
    method env = env
    method output = output
    method processed = processed

    method declare_sym
      : ID.t -> Arg.t -> as_:ID.t -> ty:term -> unit
      = fun id arg ~as_ ~ty ->
        if not (self#has_declared id arg) then (
          (* only declare once *)
          self#done_declaring id arg;
          let env_info = Env.find_exn ~env id in
          let loc = env_info.Env.loc in
          self#push_res
            (Stmt.mk_decl ~info:{Stmt.loc; name=None}
              as_ env_info.Env.decl_kind ty);
        )

    (* recursive traversal of terms *)
    method virtual do_term : depth:int -> term -> term

    method do_var
    : depth:int -> term Var.t -> term Var.t
    = fun ~depth v -> Var.update_ty v ~f:(self#do_term ~depth)

    (* transformation of this particular definition *)
    method virtual do_def
      : depth:int -> (term, term, 'inv1) Stmt.rec_def -> Arg.t -> (term, term, 'inv2) Stmt.rec_def list

    method do_def_rec
    : depth:int -> loc:Loc.t option ->
      (term, term, 'inv1) Stmt.rec_defs ->
      (term, term, 'inv1) Stmt.rec_def -> Arg.t -> unit
    = fun ~depth ~loc _defs def arg ->
      let id = def.Stmt.rec_defined.Stmt.defined_head in
      Utils.debugf ~section 3
        "@[<2>process rec case `%a` for@ (%a)@ at depth %d@]"
        (fun k -> k ID.print id Arg.print arg depth);
      let l = UF_list.make [] in
      let frame = {
        sf_id=id;
        sf_def=`Defs l;
        sf_is_root=true;
      } in
      self#push frame;
      self#in_processing id arg frame;
      (* transform [def] and push it into [l] *)
      let new_defs = self#do_def ~depth def arg in
      UF_list.append new_defs l;
      if frame.sf_is_root then (
        (* at root, make statement *)
        let res = UF_list.find_res l in
        Utils.debugf ~section 5
          "@[<2>rec case `%a`@ is root of mutual block@ @[%a@]@]"
          (fun k->k ID.print id (CCFormat.list PStmt.print_rec_def) res);
        let stmt = Stmt.axiom_rec ~info:{Stmt.name=None; loc;} res in
        self#push_res stmt
      );
      self#pop;
      self#done_processing id arg;
      ()

    method virtual do_pred
    : depth:int ->
      [`Wf | `Not_wf] -> [`Pred | `Copred] ->
      (term, term, 'inv1) Stmt.pred_def -> Arg.t ->
      (term, term, 'inv2) Stmt.pred_def list

    (* how does well-foundedness translate? *)
    method pred_translate_wf
      : [`Wf | `Not_wf] -> [`Wf | `Not_wf]
      = fun wf -> wf

    method do_pred_rec
    : depth:int -> loc:Loc.t option ->
      [`Wf | `Not_wf] -> [`Pred | `Copred] ->
      (term, term, 'inv1) Stmt.pred_def list ->
      (term, term, 'inv1) Stmt.pred_def ->
      Arg.t ->
      unit
    = fun ~depth ~loc wf kind _defs def arg ->
      let id = def.Stmt.pred_defined.Stmt.defined_head in
      Utils.debugf ~section 3
        "@[<2>process pred `%a` for@ (%a %a)@ at depth %d@]"
        (fun k -> k ID.print def.Stmt.pred_defined.Stmt.defined_head
          ID.print id Arg.print arg depth);
      let l = UF_list.make [] in
      let frame = {
        sf_id=id;
        sf_def = `Preds (wf, kind, l);
        sf_is_root=true;
      } in
      self#push frame;
      self#in_processing id arg frame;
      let new_preds = self#do_pred ~depth wf kind def arg in
      UF_list.append new_preds l;
      if frame.sf_is_root then (
        let res = UF_list.find_res l in
        Utils.debugf ~section 5
          "@[<2>pred `%a`@ is root of mutual block@ @[%a@]@]"
          (fun k->k ID.print id (CCFormat.list PStmt.print_pred_def) res);
        let wf' = self#pred_translate_wf wf in
        let stmt = Stmt.mk_pred ~info:{Stmt.name=None; loc;} ~wf:wf' kind res in
        self#push_res stmt
      );
      self#pop;
      self#done_processing id arg;
      ()

    method virtual do_copy
    : depth:int -> loc:Loc.t option ->
      (term, term) Stmt.copy -> Arg.t -> unit

    method virtual do_spec
    : depth:int -> loc:Loc.t option -> ID.t ->
      (term, term) Stmt.spec_defs -> Arg.t ->
      unit

    method virtual do_mutual_types
    : depth:int -> term Stmt.tydef -> Arg.t -> term Stmt.tydef list

    (* specialize (co)inductive types *)
    method do_mutual_types_rec
    : depth:int -> loc:Loc.t option ->
      [`Data | `Codata] ->
      term Stmt.tydef list ->
      term Stmt.tydef ->
      Arg.t ->
      unit
    = fun ~depth ~loc kind _tydefs tydef arg ->
      let id = tydef.Stmt.ty_id in
      Utils.debugf ~section 3
        "@[<2>process type decl `%a : %a`@ for %a@ at depth %d@]"
        (fun k-> k ID.print id P.print tydef.Stmt.ty_type Arg.print arg depth);
      let l = UF_list.make [] in
      let frame = {
        sf_id=id;
        sf_def=`Types (kind, l);
        sf_is_root=true;
      } in
      self#push frame;
      self#in_processing id arg frame;
      let tydefs' = self#do_mutual_types ~depth tydef arg in
      UF_list.append tydefs' l;
      if frame.sf_is_root then (
        (* at the root! generate a new statement *)
        let res = UF_list.find_res l in
        let stmt = Stmt.mk_ty_def ~info:{Stmt.name=None; loc} kind res in
        self#push_res stmt;
      );
      self#pop;
      self#done_processing id arg;
      ()

    method virtual do_ty_def
    : ?loc:Loc.t -> Stmt.decl -> ID.t -> ty:term -> Arg.t -> unit

    (* traverse the stack downward, merging every frame with [f] until we
       reach [f] itself *)
    method private merge_down_to f =
      try
        List.iter
          (fun f' ->
            (* stop if [f] and [f'] are the same frame *)
            if f == f' then raise Exit;
            f'.sf_is_root <- false; (* above [f] *)
            match f.sf_def, f'.sf_def with
            | `Types (k1, l1), `Types (k2, l2) ->
                if k1=k2 then (
                  if not (UF_list.same l1 l2)
                  then Utils.debugf ~section 4
                    "specialize %a and %a in same (co)data"
                    (fun k -> k ID.print f.sf_id ID.print f'.sf_id);
                  UF_list.merge l1 l2;
                ) else
                  Arg.fail
                    "@[<2>cannot handle nested {(co)data, data}:@ @[<h>{%a, %a}@]@]"
                    ID.print f.sf_id ID.print f'.sf_id;
            | `Preds (wf1, k1, l1), `Preds (wf2, k2, l2) ->
                if wf1=wf2 && k1=k2 then (
                  if not (UF_list.same l1 l2)
                  then Utils.debugf ~section 4
                    "specialize %a and %a in same (co)predicate"
                    (fun k -> k ID.print f.sf_id ID.print f'.sf_id);
                  UF_list.merge l1 l2;
                ) else
                  Arg.fail "incompatible style of predicates for %a and %a"
                    ID.print f.sf_id ID.print f'.sf_id
            | `Defs l1, `Defs l2 ->
                if not (UF_list.same l1 l2)
                then Utils.debugf ~section 4
                  "specialize %a and %a in same recursive functions"
                  (fun k -> k ID.print f.sf_id ID.print f'.sf_id);
                UF_list.merge l1 l2
            | `Types _, _
            | `Preds _, _
            | `Defs _, _ ->
                Arg.fail
                  "@[<2>cannot make %a and %a mutually recursive,@ they \
                    are not defined the same way@]"
                  ID.print f.sf_id ID.print f'.sf_id;
          )
          stack;
        assert false  (* should have found the frame *)
      with Exit -> ()

    (* traverse [id,arg] if depth is not too high and if
       it is not already being processed *)
    method private do_statements_for_id
      : depth:int -> ID.t -> Arg.t -> unit
      = fun ~depth id arg ->
        (* check for depth limit *)
        Utils.debugf ~section 5 "@[<2>traverse statement for@ %a (%a)@]"
          (fun k->k ID.print id Arg.print arg);
        self#check_depth depth;
        if depth > depth_limit
        then assert false (* TODO: only declare type *)
        else match self#status id arg with
        | `Done -> ()
        | `In f ->
            (* merge every frame more recent than [f] with [f], and do
                nothing else *)
            self#merge_down_to f;
        | `New ->
            self#do_new_statement_for_id ~depth id arg

    (* [id,arg] not processed yet, traverse it depending on
       what its definition looks like *)
    method private do_new_statement_for_id
      : depth:int -> ID.t -> Arg.t -> unit
      = fun ~depth id arg ->
        let env_info = match Env.find ~env id with
          | None -> Arg.fail "could not find definition of %a" ID.print id
          | Some i -> i
        in
        let loc = Env.loc env_info in
        match Env.def env_info with
        | Env.Fun_spec _ when conf.direct_spec -> ()
        | Env.Fun_spec (spec,loc) ->
            self#do_spec ~depth ~loc id spec arg;
            assert (self#has_processed id arg);
        | Env.Fun_def (defs, def, loc) ->
            self#do_def_rec ~depth ~loc defs def arg;
            assert (self#has_processed id arg);
        | Env.Pred (wf, k, def, defs, loc) ->
            self#do_pred_rec ~depth ~loc wf k defs def arg;
            assert (self#has_processed id arg);
        | (Env.Cstor _ | Env.Data _) when conf.direct_mutual_types -> ()
        | Env.Cstor (_,_,tydef,_) ->
            (* instead of processing the constructor, we should always
               process the type it belongs to. *)
            self#do_statements_for_id ~depth tydef.Stmt.ty_id arg
        | Env.Data (k,tydefs,tydef) ->
            assert (ID.equal tydef.Stmt.ty_id id);
            self#do_mutual_types_rec ~depth ~loc k tydefs tydef arg;
            assert (self#has_processed id arg);
        | Env.Copy_abstract c
        | Env.Copy_concretize c
        | Env.Copy_ty c ->
            if not conf.direct_copy then (
              self#do_copy ~depth ~loc c arg;
              assert (self#has_processed c.Stmt.copy_id arg);
            )
        | Env.NoDef when conf.direct_tydef -> () (* already defined *)
        | Env.NoDef ->
            let ty = env_info.Env.ty in
            let decl = env_info.Env.decl_kind in
            let loc = env_info.Env.loc in
            self#do_ty_def ?loc decl id ~ty arg

    method update_env f = env <- f env

    (* translation of toplevel goal or axiom (default is {!do_term}) *)
    method do_goal_or_axiom
    : term -> term
    = self#do_term ~depth:0

    (* register the statement into the state's [env], so that next statements
      can refer to it. Some statements are automatically kept (goal and axiom) *)
    method do_stmt
    : (term, term, 'inv1) Stmt.t -> unit
    = fun st ->
      Utils.debugf ~section 2 "@[<2>enter statement@ `%a`@]"
        (fun k-> k PStmt.print st);
      (* process statement *)
      let info = Stmt.info st in
      let loc = Stmt.loc st in
      (* most basic processing: just traverse the terms to update dependencies *)
      let tr_term = self#do_term ~depth:0 in
      let tr_type = tr_term in
      begin match Stmt.view st with
      | Stmt.Decl (id,k,ty) ->
          (* declare the statement (in case it is needed later) *)
          env <- Env.declare ?loc ~kind:k ~env id ty;
          if conf.direct_tydef then
            let ty = tr_type ty in
            self#push_res (Stmt.mk_decl ~info id k ty)
      | Stmt.Goal g ->
          (* convert goal *)
          let g = self#do_goal_or_axiom g in
          self#push_res (Stmt.goal ~info g)
      | Stmt.Axiom (Stmt.Axiom_std l) ->
          (* keep axioms *)
          let l = List.map self#do_goal_or_axiom l in
          self#push_res (Stmt.axiom ~info l)
      | Stmt.Pred (wf, k, preds) ->
          env <- Env.def_preds ?loc ~env ~wf ~kind:k preds;
      | Stmt.Axiom (Stmt.Axiom_spec l) ->
          env <- Env.spec_funs ?loc ~env l;
          if conf.direct_spec then
            let l = Stmt.map_spec_defs ~term:tr_term ~ty:tr_type l in
            self#push_res (Stmt.axiom_spec ~info l)
      | Stmt.Axiom (Stmt.Axiom_rec l) ->
          env <- Env.rec_funs ?loc ~env l;
      | Stmt.Copy c ->
          env <- Env.add_copy ?loc ~env c;
          if conf.direct_copy then
            let c = Stmt.map_copy ~term:tr_term ~ty:tr_type c in
            self#push_res (Stmt.copy ~info c);
      | Stmt.TyDef (k, l) ->
          env <- Env.def_data ?loc ~kind:k ~env l;
          if conf.direct_tydef then
            let l = Stmt.map_ty_def ~ty:tr_type l in
            self#push_res (Stmt.mk_ty_def ~info k l)
      end
  end

end
