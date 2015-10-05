
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Pipelines for Nunchaku} *)

(** {2 Type Inference} *)

module TyInfer = struct
  module T = NunTerm_typed.Default

  (* type inference *)
  module Conv = NunTypeInference.ConvertStatement(T)

  module PrintTy = NunType_intf.Print(T.Ty)

  let print_statement = NunStatement.print T.print PrintTy.print
  let print_statement_list = NunStatement.print_list T.print PrintTy.print
end
