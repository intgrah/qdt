type ix = int
type lvl = int
type meta_id = int

type bd =
  | Bound
  | Defined

type tm =
  | Var of ix
  | Global of string (* reference to global definition by name *)
  | Lam of string * tm (* name for printing *)
  | App of tm * tm
  | U
  | Pi of string * tm * tm
  | Let of string * tm * tm * tm
  | Meta of meta_id
  | InsertedMeta of meta_id * bd list
  | Unit
  | UnitTerm
  | Prod of tm * tm (* non-dependent product A × B *)
  | Pair of tm * tm
  | Fst of tm
  | Snd of tm

type ty = tm

type frame =
  | FApp of vl
  | FFst
  | FSnd

and spine = frame list

and vl =
  | VFlex of meta_id * spine
  | VRigid of lvl * spine
  | VLam of string * closure
  | VPi of string * vl * closure
  | VU
  | VUnit
  | VUnitTerm
  | VProd of vl * vl (* non-dependent product *)
  | VPair of vl * vl

and closure = Closure of env * tm
and env = vl list

let meta_table : (meta_id, vl option) Hashtbl.t = Hashtbl.create 16

let fresh_meta () : meta_id =
  let id = Hashtbl.length meta_table in
  Hashtbl.add meta_table id None;
  id

let lookup_meta : meta_id -> vl option = Hashtbl.find meta_table

let solve_meta (id : meta_id) (v : vl) : unit =
  Hashtbl.replace meta_table id (Some v)

let reset_meta_context () : unit = Hashtbl.clear meta_table

(* Global definition table *)
type global_entry = {
  value : vl;
  ty : vl;
}

let global_table : (string, global_entry) Hashtbl.t = Hashtbl.create 16

let define_global (name : string) (value : vl) (ty : vl) : unit =
  Hashtbl.add global_table name { value; ty }

let lookup_global (name : string) : global_entry option =
  Hashtbl.find_opt global_table name

let reset_global_context () : unit = Hashtbl.clear global_table
