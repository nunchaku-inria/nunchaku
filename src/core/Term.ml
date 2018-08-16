
open TermInner

module T = struct
  type t = {
    view: t view;
  }

  let rec repr t = match t.view with
    | TyMeta {MetaVar.deref=Some t'; _} -> repr t'
    | v -> v

  let make_raw_ view = {view}

  let build view = match view with
    | App (t, []) -> t
    | App ({view=App (f, l1); _}, l2) ->
      make_raw_ (App (f, l1 @ l2))
    | _ -> make_raw_ view

  include (Util(struct
      type nonrec t = t
      let repr = repr
      let build = build
    end) : UTIL with type t := t)
  include (Print(struct type nonrec t = t let repr = repr end) : PRINT with type t := t)
end

include T

module Red = Reduce.Make(T)
module Pat = Pattern.Make(T)
