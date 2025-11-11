open Syntax

val eval : env -> tm -> val_ty
val apply_ty : val_ty -> val_ty -> val_ty
val force : val_ty -> val_ty
