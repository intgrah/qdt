let () = failwith "Do not use"

exception Unify_error of string

type meta_var = int
type lvl = int

module MetaMap = Map.Make (Int)

type meta_solution =
  | MetaTm of Syntax.tm
  | MetaTy of Syntax.ty

type meta_body = {
  mb_arguments : int;
  mb_body : meta_solution;
}

type meta_entry = {
  meta_ty : Syntax.ty;
  meta_body : meta_body option;
}

type metacontext = { metas : meta_entry MetaMap.t }

let empty_metacontext : metacontext = { metas = MetaMap.empty }

let get_meta_type (mcxt : metacontext) (m : meta_var) : Syntax.ty option =
  match MetaMap.find_opt m mcxt.metas with
  | Some entry -> Some entry.meta_ty
  | None -> None

let get_meta_body (mcxt : metacontext) (m : meta_var) : meta_body option =
  match MetaMap.find_opt m mcxt.metas with
  | Some entry -> entry.meta_body
  | None -> None

let instantiate_meta (mcxt : metacontext) (m : meta_var) (body : meta_body) :
    metacontext =
  match MetaMap.find_opt m mcxt.metas with
  | Some entry ->
      { metas = MetaMap.add m { entry with meta_body = Some body } mcxt.metas }
  | None -> raise (Unify_error "Cannot instantiate meta without type")

type constraint_ =
  | CEqual of lvl * Syntax.vl_ty * Syntax.vl_tm * Syntax.vl_ty * Syntax.vl_tm

type constraints = constraint_ list

let add_constraint (ctx : Context.t) (ty1 : Syntax.vl_ty) (t1 : Syntax.vl_tm)
    (ty2 : Syntax.vl_ty) (t2 : Syntax.vl_tm) : constraint_ =
  CEqual (ctx.lvl, ty1, t1, ty2, t2)
