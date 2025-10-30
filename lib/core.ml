type tm =
  | Var : int -> tm
  | Lambda : tm -> tm
  | App : tm * tm -> tm

type ty =
  | TVar : int -> ty
  | Pi : ty * ty -> ty
  | Star : ty

type head =
  | Local : int -> head
  | Global : string -> head

and frame = FApp : tm_value -> frame
and spine = frame list

and boundary =
  | Abstract : ty_value -> boundary
  | Translucent : tm_value -> boundary

and neutral = head * spine * boundary Lazy.t
and closure = env * tm

and tm_value =
  | LambdaV : ty_value * closure -> tm_value
  | Neutral : neutral -> tm_value

and env = tm_value list
and ty_closure = env * ty

and ty_value =
  | PiV : ty_value * ty_closure -> ty_value
  | StarV : ty_value
