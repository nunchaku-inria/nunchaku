(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Interface to Kodkod} *)

open Nunchaku_core
open Nunchaku_parsers

module Res = Problem.Res
module T = FO.T
module Ty = FO.Ty
module S = Scheduling
module E = CCResult

let name = "kodkod"
let section = Utils.Section.make name
let _kodkod_section = section

type problem = FO_rel.problem
type res = (FO_rel.expr, FO_rel.sub_universe) Problem.Res.t

module SUMap = CCMap.Make(struct
    type t = FO_rel.sub_universe
    let compare = FO_rel.su_compare
  end)

module StrMap = CCMap.Make(String)
module IntMap = CCMap.Make(CCInt)

(* names used by kodkod, based on arity *)
type kodkod_name = string

type offset = int

type state = {
  current_size: int;
  (* cardinal for sub-universes in which it's unspecified *)
  name_of_id: kodkod_name ID.Map.t;
  (* map names to kodkod names *)
  id_of_name: ID.t StrMap.t;
  (* map kodkod names to IDs *)
  univ_map: (offset * FO_rel.atom IntMap.t) SUMap.t;
  (* sub-universe ->
       its offset in the global universe
       a map from offsets to atoms of the sub-universe *)
  univ_size: int;
  (* total size of the universe *)
  decls: FO_rel.decl ID.Map.t;
  (* declarations *)
  timer: Utils.Time.timer;
  (* timer *)
}

let errorf msg = Utils.failwithf msg

let deduced_max_size pb =
  List.fold_left
    (fun m su -> match m, su.FO_rel.su_max_card with
       | None, _
       | _, None -> None
       | Some m, Some n -> Some (max m n))
    (Some 0)
    pb.FO_rel.pb_univ.FO_rel.univ_l

(* compute size of universe + offsets *)
let compute_univ_
    ~current_size
    pb
  : int * (offset * FO_rel.atom IntMap.t) SUMap.t
  =
  let open Sequence.Infix in
  let univ = pb.FO_rel.pb_univ in
  let univ_prop = univ.FO_rel.univ_prop in
  (* sub-universe for prop *)
  assert (univ_prop.FO_rel.su_max_card = Some 2 && univ_prop.FO_rel.su_min_card = 2);
  (* add other sub-universes *)
  let n, su_to_atom_map, _ =
    List.fold_left
      (fun (n,su_to_atom_map,card_to_offset_map) su ->
         (* compute cardinal *)
         let card = max current_size su.FO_rel.su_min_card in
         let card = match su.FO_rel.su_max_card with
           | None -> card
           | Some n -> min n card
         in
         (* map [n+i -> atom(su,i) for i=0...card-1] *)
         let a_to_i offset =
           0 -- (card-1)
           |> Sequence.map (fun i -> offset+i, FO_rel.atom su i)
           |> IntMap.of_seq
         in
         begin match IntMap.get card card_to_offset_map with
           | None ->
             (* update [su_to_atom_map] and [card_to_offset_map] to reflect
                the fact that [su] will be represented by the range
                [n, ..., n + card - 1] *)
             n + card,
             SUMap.add su (n, a_to_i n) su_to_atom_map,
             IntMap.add card n card_to_offset_map
           | Some offset ->
             (* there is already a domain for sub-universes of size [card],
                use it *)
             n,
             SUMap.add su (offset, a_to_i offset) su_to_atom_map,
             card_to_offset_map
         end)
      (0, SUMap.empty, IntMap.empty)
      (univ_prop :: univ.FO_rel.univ_l)
  in
  n, su_to_atom_map

(* indices for naming constants by arity *)
type name_map = int StrMap.t

(* find a unique name for some ID of arity [n], update the offsets map *)
let name_of_arity (m:name_map) n: name_map * string =
  let prefix = match n with
    | 0 (* will be encoded as unary predicate *)
    | 1 -> "s"
    | 2 -> "r"
    | n -> Printf.sprintf "m%d_" n
  in
  let offset = StrMap.get_or ~default:0 prefix m in
  let m' = StrMap.add prefix (offset+1) m in
  let name = prefix ^ string_of_int offset in
  m', name

(* map atom names to Kodkodi identifiers *)
let translate_names_ pb =
  let _,n2id,id2n =
    ID.Map.fold
      (fun _ decl (nm,n2id,id2n) ->
         let id = decl.FO_rel.decl_id in
         let nm, name = name_of_arity nm decl.FO_rel.decl_arity in
         nm, StrMap.add name id n2id, ID.Map.add id name id2n
      )
      pb.FO_rel.pb_decls
      (StrMap.empty,StrMap.empty,ID.Map.empty)
  in
  n2id, id2n

(* initialize the state for this particular problem *)
let create_state ~timer ~current_size (pb:FO_rel.problem) : state =
  let univ_size, univ_map = compute_univ_ ~current_size pb in
  let id_of_name, name_of_id = translate_names_ pb in
  { current_size;
    name_of_id;
    id_of_name;
    univ_size;
    univ_map;
    timer;
    decls= pb.FO_rel.pb_decls;
  }

let fpf = Format.fprintf
let pp_list ~sep pp = Utils.pp_list ~sep pp

type rename_kind =
  | R_quant (* quantifier *)
  | R_let of [`Form | `Rel] (* let binding *)

(* print in kodkodi syntax *)
let pp_pb state pb out () : unit =
  (* local substitution for renaming variables *)
  let subst : (FO_rel.var_ty, string) Var.Subst.t ref = ref Var.Subst.empty in
  let id2name id =
    try ID.Map.find id state.name_of_id
    with Not_found -> errorf "kodkod: no name for `%a`" ID.pp id
  and su2offset su =
    try SUMap.find su state.univ_map
    with Not_found ->
      errorf "kodkod: no offset for `%a`" FO_rel.pp_sub_universe su
  in
  (* print a sub-universe as a range *)
  let rec pp_su_range out (su:FO_rel.sub_universe): unit =
    let offset, atoms = su2offset su in
    let card = IntMap.cardinal atoms in
    if offset=0
    then fpf out "u%d" card
    else fpf out "u%d@@%d" card offset
  (* print a sub-universe's name *)
  and pp_su_name out su: unit =
    fpf out "%s" (id2name su.FO_rel.su_name)
  and pp_atom out (a:FO_rel.atom): unit =
    let offset, _ = su2offset a.FO_rel.a_sub_universe in
    fpf out "A%d" (offset + a.FO_rel.a_index)
  and pp_tuple out (tuple:FO_rel.tuple) =
    fpf out "[@[%a@]]" (pp_list ~sep:", " pp_atom) tuple
  and pp_ts out (ts:FO_rel.tuple_set): unit = match ts with
    | FO_rel.TS_all su -> pp_su_range out su
    | FO_rel.TS_list l ->
      fpf out "{@[%a@]}" (pp_list ~sep:", " pp_tuple) l
    | FO_rel.TS_product l ->
      fpf out "%a" (pp_list ~sep:" -> " pp_ts) l
  and pp_form out = function
    | FO_rel.False -> fpf out "false"
    | FO_rel.True -> fpf out "true"
    | FO_rel.Eq (a,b) ->
      fpf out "(@[<2>%a@ = %a@])" pp_rel a pp_rel b
    | FO_rel.In (a,b) ->
      fpf out "(@[<2>%a@ in %a@])" pp_rel a pp_rel b
    | FO_rel.Mult (m,e) ->
      let s = match m with
        | FO_rel.M_no -> "no"
        | FO_rel.M_one -> "one"
        | FO_rel.M_lone -> "lone"
        | FO_rel.M_some -> "some"
      in
      fpf out "@[<2>%s@ %a@]" s pp_rel e
    | FO_rel.Not f -> fpf out "(! %a)" pp_form f
    | FO_rel.And l ->
      fpf out "(@[<hv>%a@])" (pp_list ~sep:" && " pp_form) l
    | FO_rel.Or l ->
      fpf out "(@[<hv>%a@])" (pp_list ~sep:" || " pp_form) l
    | FO_rel.Imply (a,b) ->
      fpf out "(@[<2>%a@ => %a@])" pp_form a pp_form b
    | FO_rel.Equiv (a,b) ->
      fpf out "(@[<2>%a@ <=> %a@])" pp_form a pp_form b
    | FO_rel.Forall (v,f) -> pp_binder "all" out v f
    | FO_rel.Exists (v,f) -> pp_binder "some" out v f
    | FO_rel.F_let (v,a,b) ->
      within_rename ~k:(R_let `Rel) v
        ~f:(fun name ->
          fpf out "(@[<2>let@ [@[%s := %a@]]@ | %a@])" name pp_rel a pp_form b)
    | FO_rel.F_if (a,b,c) ->
      fpf out "(@[<2>if %a@ then %a@ else %a@])"
        pp_form a pp_form b pp_form c
    | FO_rel.Int_op (FO_rel.IO_leq, a, b) ->
      fpf out "(@[<>%a@ <= %a@])" pp_ie a pp_ie b
  (* rename [v] temporarily, giving its name to [f] *)
  and within_rename ~(k:rename_kind) v ~f =
    let n = Var.Subst.size !subst in
    let name = match k with
      | R_quant -> Printf.sprintf "S%d'" n
      | R_let `Form -> Printf.sprintf "$f%d" n
      | R_let `Rel -> Printf.sprintf "$e%d" n
    in
    subst := Var.Subst.add ~subst:!subst v name;
    CCFun.finally1
      ~h:(fun () -> subst := Var.Subst.remove ~subst:!subst v)
      f name
  and pp_binder b out v f =
    within_rename ~k:R_quant v
      ~f:(fun name ->
        fpf out "(@[<2>%s [%s : one %a]@ | %a@])"
          b name pp_su_name (Var.ty v) pp_form f)
  and pp_ie out (e:FO_rel.int_expr): unit = match e with
    | FO_rel.IE_cst n -> fpf out "%d" n
    | FO_rel.IE_card e -> fpf out "#(@[%a@])" pp_rel e
    | FO_rel.IE_sum e -> fpf out "sum(@[%a@])" pp_rel e
  and pp_rel out = function
    | FO_rel.Const id -> CCFormat.string out (id2name id )
    | FO_rel.None_  -> CCFormat.string out "none"
    | FO_rel.Tuple_set ts -> pp_ts out ts
    | FO_rel.Var v ->
      begin match Var.Subst.find ~subst:!subst v with
        | None -> errorf "var `%a` not in scope" Var.pp_full v
        | Some s -> CCFormat.string out s
      end
    | FO_rel.Unop (FO_rel.Flip, e) -> fpf out "~ %a" pp_rel e
    | FO_rel.Unop (FO_rel.Trans, e) -> fpf out "* %a" pp_rel e
    | FO_rel.Binop (FO_rel.Union, a, b) ->
      fpf out "(@[<2>%a +@ %a@])" pp_rel a pp_rel b
    | FO_rel.Binop (FO_rel.Inter, a, b) ->
      fpf out "(@[<2>%a &@ %a@])" pp_rel a pp_rel b
    | FO_rel.Binop (FO_rel.Diff, a, b) ->
      fpf out "(@[<2>%a \\@ %a@])" pp_rel a pp_rel b
    | FO_rel.Binop (FO_rel.Join, a, b) ->
      fpf out "(@[<2>%a . %a@])" pp_rel a pp_rel b
    | FO_rel.Binop (FO_rel.Product, a, b) ->
      fpf out "(@[<2>%a ->@ %a@])" pp_rel a pp_rel b
    | FO_rel.If (a,b,c) ->
      fpf out "(@[<2>if %a@ then %a@ else %a@])"
        pp_form a pp_rel b pp_rel c
    | FO_rel.Comprehension (v,f) ->
      within_rename ~k:R_quant v
        ~f:(fun name ->
          fpf out "{@[<2>%s |@ %a@]}" name pp_form f)
    | FO_rel.Let (v,t,u) ->
      within_rename ~k:(R_let `Rel) v
        ~f:(fun name ->
          fpf out "(@[<2>let@ [@[%s := %a@]]@ | %a@])" name pp_rel t pp_rel u)
  in
  (* go! prelude first *)
  fpf out "/* emitted from Nunchaku */@.";
  (* settings *)
  fpf out "solver: \"Lingeling\"@.";
  let n_digits = 32 in
  fpf out "bit_width : %d@." n_digits;
  (* universe *)
  fpf out "univ: u%d@." state.univ_size;
  (* decls *)
  ID.Map.iter
    (fun _ d ->
       let id = d.FO_rel.decl_id in
       let name = ID.Map.find id state.name_of_id in
       fpf out "@[<h>bounds %s /* %a */ : [%a, %a] @."
         name ID.pp id pp_ts d.FO_rel.decl_low pp_ts d.FO_rel.decl_high)
    pb.FO_rel.pb_decls;
  (* goal *)
  fpf out "@[<v2>solve@ %a;@]@."
    (pp_list ~sep:" &&" pp_form) pb.FO_rel.pb_goal;
  ()

module A = Ast_kodkod

let find_atom_ state (su:FO_rel.sub_universe) (i:int) : FO_rel.atom =
  try
    SUMap.find su state.univ_map
    |> snd
    |> IntMap.find i
  with Not_found -> errorf "model parsing: could not find atom for A%d" i

(* convert the raw parse model into something more usable *)
let convert_model state (m:A.model): (FO_rel.expr,FO_rel.sub_universe) Model.t =
  let module M = Model in
  (* now build a proper model *)
  List.fold_left
    (fun m'' {A.rel_name; rel_dom} ->
       let id =
         try StrMap.find rel_name state.id_of_name
         with Not_found -> errorf "could not find ID corresponding to `%s`" rel_name
       in
       (* find the [FO_rel.decl], then use it to decode atoms depending
          on their type *)
       let decl =
         try ID.Map.find id state.decls
         with Not_found -> errorf "could not find declaration for %a" ID.pp id
       in
       (* convert offsets to proper atoms *)
       let tuples =
         rel_dom
         |> List.map
           (fun l ->
              assert (List.length l = List.length decl.FO_rel.decl_dom);
              List.map2 (find_atom_ state)
                decl.FO_rel.decl_dom
                l)
       in
       (* add to model *)
       let t = FO_rel.const id in
       let u = FO_rel.tuple_set (FO_rel.ts_list tuples) in
       M.add_const m'' (t,u,M.Symbol_prop))
    M.empty
    m

let mk_info state: Res.info =
  Res.mk_info
    ~message:(Printf.sprintf "dimension %d" state.current_size)
    ~backend:"kodkod"
    ~time:(Utils.Time.get_timer state.timer) ()

module Parser = struct
  module L = Lex_kodkod
  module P = Parse_kodkod

  let parse_errorf lexbuf msg =
    let loc = Location.of_lexbuf lexbuf in
    Parsing_utils.parse_error_ ~loc
      ("kodkod: " ^^ msg)

  type 'a t = Lexing.lexbuf -> 'a

  let filter_ ~msg ~f lexbuf =
    let t = L.token lexbuf in
    match f t with
      | Some x -> x
      | None -> parse_errorf lexbuf "expected %s" msg

  (* expect exactly [t] *)
  let exactly ~msg t = filter_ ~msg ~f:(fun t' -> if t=t' then Some () else None)

  let section : A.section t =
    filter_ ~msg:"outcome" ~f:(function P.SECTION s -> Some s | _ -> None)

  let outcome lexbuf : unit = match section lexbuf with
    | A.S_outcome -> ()
    | _ -> parse_errorf lexbuf "wrong section, expected OUTCOME"

  let instance lexbuf : unit = match section lexbuf with
    | A.S_instance -> ()
    | _ -> parse_errorf lexbuf "wrong section, expected INSTANCES"

  let ident : string t =
    filter_ ~msg:"ident" ~f:(function P.IDENT s -> Some s | _ -> None)

  let colon : unit t = exactly ~msg:"`:`" P.COLON

  (* parse the result from the solver's stdout and errcode *)
  let res state (s:string) (errcode:int) : res * S.shortcut =
    let info = mk_info state in
    if errcode = 137
    then (
      Utils.debugf ~section:_kodkod_section 1
        "kodkod stopped with errcode %d, assume it timeouted; stdout:@ `%s`"
        (fun k->k errcode s);
      Res.Unknown [Res.U_timeout info], S.No_shortcut
    )
    else if errcode <> 0 && CCString.mem s ~sub:"Ran out of time"
    then Res.Unknown [Res.U_timeout info], S.No_shortcut
    else if errcode <> 0
    then (
      let msg = CCFormat.sprintf "kodkod failed (errcode %d), stdout:@ `%s`@." errcode s in
      Res.Unknown [Res.U_backend_error (info, msg)], S.No_shortcut
    ) else (
      let delim = "---OUTCOME---" in
      let i =
        try CCString.find ~sub:delim s
        with Not_found -> errorf "could not find end delimiter in Kodkod's output"
      in
      assert (i>=0);
      let s' = String.sub s i (String.length s - i) in
      let lexbuf = Lexing.from_string s' in
      outcome lexbuf;
      match L.result lexbuf with
        | A.Unsat
        | A.Trivially_unsat ->
          Res.Unsat info, S.Shortcut
        | A.Sat ->
          (* parse model *)
          instance lexbuf;
          let i = ident lexbuf in
          if i <> "relations"
          then parse_errorf lexbuf "expected `relations`, got `%s`" i;
          colon lexbuf;
          let m = Parse_kodkod.parse_model L.token lexbuf in
          let m = convert_model state m in
          Res.Sat (m,info), S.Shortcut
    )
end

let solve ~deadline state pb : res * Scheduling.shortcut =
  Utils.debug ~section 1 "calling kodkod";
  let now = Unix.gettimeofday() in
  if now +. 0.5 > deadline
  then
    let i = Res.mk_info ~backend:"kodkod" ~time:0. () in
    Res.Unknown [Res.U_timeout i], S.No_shortcut
  else (
    (* print the problem *)
    let timeout = deadline -. now in
    let kodkod_timeout = int_of_float (ceil ((deadline -. now) *. 1000.)) in
    let hard_timeout = (int_of_float (timeout +. 1.5)) in
    let cmd =
      Printf.sprintf "ulimit -t %d; kodkodi -max-msecs %d 2>&1"
        hard_timeout kodkod_timeout
    in
    (* call solver, get its stdout and errcode *)
    let fut =
      S.popen cmd
        ~f:(fun (stdin,stdout) ->
          (* send problem *)
          let fmt = Format.formatter_of_out_channel stdin in
          Format.fprintf fmt "%a@." (pp_pb state pb) ();
          flush stdin;
          close_out stdin;
          CCIO.read_all stdout)
    in
    match S.Fut.get fut with
      | S.Fut.Done (E.Ok (stdout, errcode)) ->
        Utils.debugf ~lock:true ~section 2
          "@[<2>kodkod exited with %d, stdout:@ `%s`@]"
          (fun k->k errcode stdout);
        Parser.res state stdout errcode
      | S.Fut.Done (E.Error e) ->
        Res.Unknown [Res.U_backend_error (mk_info state, Printexc.to_string e)],
        S.No_shortcut
      | S.Fut.Stopped ->
        Res.Unknown [Res.U_timeout (mk_info state)], S.No_shortcut
      | S.Fut.Fail e ->
        (* return error *)
        Utils.debugf ~lock:true ~section 1 "@[<2>kodkod failed with@ `%s`@]"
          (fun k->k (Printexc.to_string e));
        Res.Unknown [Res.U_backend_error (mk_info state, Printexc.to_string e)],
        S.No_shortcut
  )

let default_min_size = 4 (* FUDGE *)
let default_size_increment = 4 (* FUDGE *)

(* call {!solve} with increasingly big problems, until we run out of time
   or obtain "sat" *)
let rec call_rec ~timer ~print ~size ~max_size ~size_increment ~deduced_max_size ~deadline pb
    : res * Scheduling.shortcut =
  let state = create_state ~timer ~current_size:size pb in
  if print
  then Format.printf "@[<v>kodkod problem:@ ```@ %a@,```@]@." (pp_pb state pb) ();
  let res, short = solve ~deadline state pb in
  Utils.debugf ~section 2 "@[<2>kodkod result for size %d:@ %a@]"
    (fun k->k size Res.pp_head res);
  match res with
    | Res.Unsat i ->
      let now = Unix.gettimeofday () in
      let deduced_max_size_reached =
        match deduced_max_size with None -> false | Some n -> size >= n
      in
      let max_size_reached =
        match max_size with None -> false | Some n -> size >= n
      in
      if deduced_max_size_reached then (
        Utils.debug ~section 2 "kodkod found unsat and all domains have bounded cardinality";
        Res.Unsat i, S.Shortcut
      ) else if max_size_reached then (
        Utils.debug ~section 2 "reached specified maximal cardinality bound";
        Res.Unknown [Res.U_incomplete i], S.No_shortcut
      ) else if deadline -. now > 0.5 then (
        (* unsat, and we still have some time: retry with a bigger size *)
        let next_size = size + size_increment in
        let next_size = match deduced_max_size with None -> next_size | Some n -> min n next_size in
        let next_size = match max_size with None -> next_size | Some n -> min n next_size in
        call_rec ~timer ~print ~size:next_size ~max_size ~size_increment ~deduced_max_size
          ~deadline pb
      ) else (
        (* maybe there's a larger model, but we have no time left *)
        Res.Unknown [Res.U_incomplete i], S.No_shortcut
      )
    | _ -> res, short

let call_real ~min_size ~max_size ~size_increment ~print_model ~prio ~print pb =
  S.Task.make ~prio
    (fun ~deadline () ->
       let timer = Utils.Time.start_timer () in
       let deduced_max_size = deduced_max_size pb in
       let res, short =
         call_rec ~timer ~print ~deadline ~size:min_size ~size_increment ~max_size
           ~deduced_max_size:deduced_max_size pb
       in
       begin match res with
         | Res.Sat (m,_) when print_model ->
           let pp_ty oc _ = CCFormat.string oc "$i" in
           Format.printf "@[<2>@{<Yellow>raw kodkod model@}:@ @[%a@]@]@."
             (Model.pp (CCFun.const FO_rel.pp_expr) pp_ty) m
         | _ -> ()
       end;
       res, short)

let call ?(print_model=false) ?(prio=10) ?(min_size=default_min_size) ?max_size
    ?(size_increment=default_size_increment) ~print ~dump pb
  =
  if size_increment < 1 then errorf "kodkod: illegal size increment %d" size_increment;
  match dump with
  | None ->
    call_real ~min_size ~max_size ~size_increment ~print_model ~prio ~print pb
  | Some file ->
    (* TODO: emit sequence of problems for different sizes? *)
    let file = file ^ ".kodkod.kki" in
    Utils.debugf ~section 1 "output kodkod problem into `%s`" (fun k->k file);
    CCIO.with_out file
      (fun oc ->
         let out = Format.formatter_of_out_channel oc in
         let state = create_state ~timer:(Utils.Time.start_timer())
           ~current_size:min_size pb
         in
         Format.fprintf out
           "@[<v>%a@]@."
           (pp_pb state pb) ());
    let i = Res.mk_info ~backend:"kodkod" ~time:0. () in
    S.Task.return (Res.Unknown [Res.U_other (i, "--dump")]) S.No_shortcut

let is_available () =
  try Sys.command "which kodkodi > /dev/null 2> /dev/null" = 0
  with Sys_error _ -> false

let pipe ?(print_model=false) ?min_size ?max_size ?size_increment ~print ~dump () =
  let encode pb = call ?min_size ?max_size ?size_increment ~print_model ~print ~dump pb, () in
  Transform.make
    ~name
    ~encode
    ~decode:(fun _ res -> res)
    ()
