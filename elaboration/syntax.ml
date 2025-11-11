type ix = int
type lvl = int
type meta_id = int

type bd =
  | Bound
  | Defined

type tm =
  | Var of ix
  | Lam of string * tm (* name for printing *)
  | App of tm * tm
  | U
  | Pi of string * tm * tm
  | Let of string * tm * tm * tm
  | Meta of meta_id
  | InsertedMeta of meta_id * bd list

type ty = tm

type val_ty =
  | VFlex of meta_id * spine
  | VRigid of lvl * spine
  | VLam of string * closure
  | VPi of string * val_ty * closure
  | VU

and closure = Closure of env * tm
and env = val_ty list
and spine = val_ty list

let meta_table : (meta_id, val_ty option) Hashtbl.t = Hashtbl.create 16

let fresh_meta () : meta_id =
  let id = Hashtbl.length meta_table in
  Hashtbl.add meta_table id None;
  id

let lookup_meta : meta_id -> val_ty option = Hashtbl.find meta_table

let solve_meta (id : meta_id) (v : val_ty) : unit =
  Hashtbl.replace meta_table id (Some v)

let reset_meta_context () : unit = Hashtbl.clear meta_table
