
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Pipelines for Nunchaku} *)

module Tr = NunTransform

(** {2 Type Inference} *)

module TyInfer = struct
  module T = NunTerm_typed.Default

  (* type inference *)
  module Conv = NunTypeInference.ConvertStatement(T)

  module PrintTy = NunType_intf.Print(T.Ty)

  let print_statement = NunStatement.print T.print PrintTy.print
  let print_statement_list = NunStatement.print_list T.print PrintTy.print

  (* TODO: actually use Term_ho and compute signature, etc. *)

  let pipe = Tr.make
    ~name:"type inference"
    ~encode:(fun l -> CCKList.singleton (Conv.convert_list_exn ~env:Conv.empty_env l))
    ~decode:(fun _ _ -> assert false)
end
