type name = string

type tm =
  | Var : name -> tm
  | Lambda : name * ty option * tm -> tm
  | App : tm * tm -> tm
  | Ann : tm * ty -> tm
  | Hole : tm

and ty =
  | TVar : name -> ty
  | Pi : name * ty * ty -> ty
  | Arrow : ty * ty -> ty
  | Star : ty
