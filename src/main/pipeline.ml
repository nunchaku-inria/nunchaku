
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Pipelines for Nunchaku} *)

module ID = NunID
module Tr = NunTransform
module Utils = NunUtils

module Res = struct
  type 't model = 't NunProblem.Model.t

  type 't t =
    | Unsat
    | Sat of 't model  (** model maps terms to values *)
    | Timeout

  let map ~f t = match t with
    | Unsat -> Unsat
    | Timeout -> Timeout
    | Sat model -> Sat (NunProblem.Model.map ~f model)

  let fpf = Format.fprintf

  let print pt out = function
    | Unsat -> fpf out "unsat"
    | Timeout -> fpf out "timeout"
    | Sat m ->
        fpf out "@[<2>sat {@,%a}@]" (NunProblem.Model.print pt) m
end

(** {2 Type Inference} *)

let ty_infer (type a) (type b) ~print
(module T1 : NunTerm_typed.S with type t = a)
(module T2 : NunTerm_ho.S with type t = b) =
  let module PrintT = NunTerm_ho.Print(T1) in
  (* we get back "regular" HO terms *)
  let module Erase = NunTerm_ho.Erase(T2) in
  (* type inference *)
  let module Conv = NunTypeInference.Convert(T1) in
  let print_problem = NunProblem.print PrintT.print T1.Ty.print in
  let on_encoded =
    if print
    then [Format.printf "@[<2>after type inference:@ %a@]@." print_problem]
    else []
  in
  Tr.make1
    ~on_encoded
    ~name:"type inference"
    ~encode:(fun l ->
      let problem = l
        |> Conv.convert_problem_exn ~env:Conv.empty_env
        |> fst
      in
      problem, ()
    )
    ~decode:(fun () (model : T2.t Res.model) ->
      let ctx = Erase.create () in
      NunProblem.Model.map model ~f:(Erase.erase ~ctx)
    ) ()

(** {2 Optimizations/Encodings} *)

let mono (type a)(type b) ~print
(module T1 : NunTerm_ho.VIEW with type t = a)
(module T2 : NunTerm_ho.S with type t = b)
=
  let module Mono = NunMonomorphization.Make(T1)(T2) in
  let on_encoded = if print
    then
      let module P = NunTerm_ho.Print(T2) in
      [Format.printf "@[<2>after mono:@ %a@]@."
        (NunProblem.print P.print P.print_ty)]
    else []
  in
  Tr.make1
    ~on_encoded
    ~name:"monomorphization"
    ~encode:(fun p ->
      let sigma = NunProblem.signature p in
      let instances = Mono.compute_instances ~sigma p in
      let state = Mono.create () in
      let p = Mono.monomorphize ~instances ~state p in
      p, state
      (* TODO mangling of types, as an option *)
    )
    ~decode:(fun _ m -> m)
    ()

(** {2 Conversion to FO} *)

let to_fo (type a)(type b)
(module T : NunTerm_ho.S with type t = a)
(module FO : NunFO.S with type T.t = b) =
  let module Sol = NunSolver_intf in
  let module Conv = NunTerm_ho.AsFO(T) in
  let module ConvBack = NunTerm_ho.OfFO(T)(FO) in
  Tr.make1
  ~name:"to_fo"
  ~encode:(fun (pb:(T.t, T.ty) NunProblem.t) ->
    let pb' = Conv.convert_problem pb in
    pb', ()
  )
  ~decode:(fun _st (m:FO.T.t Res.model) ->
    ConvBack.convert_model m
  )
  ()

(** {2 Solving} *)

(* solve problem using CVC4 before [deadline] *)
let call_cvc4 (type f)(type t)(type ty)
(module FO : NunFO.VIEW with type T.t=t and type formula=f and type Ty.t=ty)
~print ~deadline problem =
  let module FOBack = NunFO.Default in
  let module P = NunFO.Print(FO) in
  let module Sol = NunSolver_intf in
  let module CVC4 = NunCVC4.Make(FO) in
  (* how much time remains *)
  let timeout = deadline -. Unix.gettimeofday() in
  if timeout < 0.1 then Res.Timeout
  else (
    if print
      then Format.printf "@[<2>FO problem:@ %a@]@." P.print_problem problem;
    let solver = CVC4.solve ~timeout problem in
    match CVC4.res solver with
    | Sol.Res.Sat m ->
        let m = ID.Map.fold
          (fun id v acc -> (FOBack.T.const id, v) :: acc)
          m []
        in
        Res.Sat m
    | Sol.Res.Unsat -> Res.Unsat
    | Sol.Res.Timeout -> Res.Timeout
    | Sol.Res.Error e ->
        failwith e
  )

(* close a pipeline with CVC4 *)
let close_pipe_cvc4 (type f)(type t)(type ty)
(module FO : NunFO.VIEW with type T.t=t and type formula=f and type Ty.t=ty)
~pipe ~print ~deadline
=
  let module FOBack = NunFO.Default in
  let module P = NunFO.Print(FOBack) in
  NunTransform.ClosedPipe.make1
    ~pipe
    ~f:(call_cvc4 (module FO) ~deadline ~print)
