open Syntax

val eval : env -> tm -> vl
val apply_frame : vl -> frame -> vl
val force : vl -> vl
