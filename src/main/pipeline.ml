
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Pipelines for Nunchaku} *)

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

module TyInfer = struct
  module T = NunTerm_typed.Default
  module PrintT = NunTerm_typed.Print(T)

  (* we get back "regular" HO terms *)
  module TBack = NunTerm_ho.Default
  module Erase = NunTerm_ho.Erase(TBack)

  (* type inference *)
  module Conv = NunTypeInference.ConvertStatement(T)

  let print_problem = NunProblem.print PrintT.print T.Ty.print

  let pipe = Tr.make
    ~name:"type inference"
    ~encode:(fun l ->
      let problem = l
        |> Conv.convert_list_exn ~env:Conv.empty_env
        |> fst
        |> (fun l->NunProblem.make l)
      in
      CCKList.singleton (problem, ())
    )
    ~decode:(fun () (model : TBack.t Res.model) ->
      let ctx = Erase.create () in
      NunProblem.Model.map model ~f:(Erase.erase ~ctx)
    ) ()
end

(** {2 Optimizations/Encodings} *)

module Mono = struct
  module T1 = NunTerm_typed.Default
  module T2 = NunTerm_ho.Default

  module DoIt = NunMonomorphization.Make(T1)(T2)

  let pipe = Tr.make
    ~name:"monomorphization"
    ~encode:(fun p -> p
        |> DoIt.encode_problem
        |> CCKList.singleton
    )
    ~decode:DoIt.decode_model
    ()
end


(** {2 Conversion to FO} *)

module ToFO = struct
  module T = NunTerm_ho.Default
  module FO = NunFO.Default
  module Sol = NunSolver_intf

  type state = unit (* TODO *)

  let print_problem = NunCVC4.print_problem

  (* TODO *)

  let pipe = Tr.make
    ~name:"to_fo"
    ~encode:(fun (_problem:(T.t, T.ty) NunProblem.t) ->
      (assert false : ((Sol.Problem.t * state) CCKList.t))
    )
    ~decode:(fun _st (_model:FO.T.t Res.model) -> (assert false : T.t Res.model))
    ()
end

(** {2 Solving} *)

module CallCVC4 = struct
  module FO = NunFO.Default
  module Sol = NunSolver_intf

  (* solve problem using CVC4 before [deadline] *)
  let solve
    : deadline:float -> Sol.Problem.t -> FO.T.t Res.t
    = fun ~deadline problem ->
      (* how much time remains *)
      let timeout = deadline -. Unix.gettimeofday() in
      if timeout < 0.1 then Res.Timeout
      else
        let solver = NunCVC4.solve ~timeout problem in
        match NunCVC4.res solver with
        | Sol.Res.Sat _m -> assert false (* TODO: extract values for terms in [problem]  *)
        | Sol.Res.Unsat -> Res.Unsat
        | Sol.Res.Timeout -> Res.Timeout
        | Sol.Res.Error e ->
            failwith e
end
