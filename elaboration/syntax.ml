type ix = int
type lvl = int
type meta_id = int

type tm =
  | Var of ix
  | Lam of ty * tm
  | App of tm * tm
  | Meta of meta_id

and ty =
  | TVar of ix
  | Pi of ty * ty
  | Type

type meta_entry =
  | Unsolved
  | Solved of tm_val

and frame = FApp of tm_val * ty_val
and spine = frame list

and boundary =
  | Abstract of ty_val
  | Translucent of tm_val

and head =
  | HVar of lvl
  | HMeta of meta_id

and neutral = {
  head : head;
  spine : spine;
  boundary : boundary Lazy.t;
}

and tm_val =
  | VLam of tm_closure
  | VNeutral of neutral

and ty_val =
  | VPi of ty_val * ty_closure
  | VType
  | VNeutral of neutral

and tm_closure = Closure_tm of env * tm
and ty_closure = Closure_ty of env * ty

and value =
  | TmVal of tm_val
  | TyVal of ty_val

and env = value list

let meta_table : (meta_id, meta_entry) Hashtbl.t = Hashtbl.create 16

let fresh_meta () : meta_id =
  let id = Hashtbl.length meta_table in
  Hashtbl.add meta_table id Unsolved;
  id

let lookup_meta : meta_id -> meta_entry = Hashtbl.find meta_table

let solve_meta (id : meta_id) (v : tm_val) : unit =
  Hashtbl.replace meta_table id (Solved v)
