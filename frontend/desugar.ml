open Raw_syntax

let desugar_sigma ((names, fst_ty) : typed_binder_group) (snd_ty : t) : t =
  List.fold_right
    (fun name acc ->
      App (Ident "Sigma", Lam ([ Typed ([ name ], fst_ty) ], acc)))
    names snd_ty

let desugar_prod (fst_ty : t) (snd_ty : t) : t =
  App (App (Ident "Prod", fst_ty), snd_ty)

let rec desugar_nat_lit : int -> t = function
  | 0 -> Ident "Nat.zero"
  | n -> App (Ident "Nat.succ", desugar_nat_lit (n - 1))

let desugar_add (a : t) (b : t) : t = App (App (Ident "Nat.add", a), b)
let desugar_sub (a : t) (b : t) : t = App (App (Ident "Nat.sub", a), b)
