
(** {1 Default Implementation of Terms} *)

include TermInner.FULL

module Red : Reduce.S with type term := t
module Pat : Pattern.S with type term := t
