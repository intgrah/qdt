val ( |- ) : Syntax.tm -> Syntax.tm -> Syntax.tm
val ( |-- ) : Syntax.tm -> Syntax.tm list -> Syntax.tm
val ( @-> ) : string option * Syntax.ty -> Syntax.ty -> Syntax.ty
val ( @--> ) : (string option * Syntax.ty) list -> Syntax.ty -> Syntax.ty
val ( @=> ) : string option * Syntax.ty -> Syntax.tm -> Syntax.tm
val ( @==> ) : (string option * Syntax.ty) list -> Syntax.tm -> Syntax.tm
val vars : int -> int -> Syntax.tm list
val shift_ty : int -> int -> Syntax.ty -> Syntax.ty
val shift_tm : int -> int -> Syntax.tm -> Syntax.tm
