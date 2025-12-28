open Syntax

type entry = {
  name : string option;
  ty : vl_ty;
}

type t = {
  entries : entry list;
  env : env;
  lvl : int;
}

let empty = { entries = []; env = []; lvl = 0 }

let bind name ty ctx =
  let var = VTmNeutral (HVar (Lvl ctx.lvl), []) in
  {
    entries = { name; ty } :: ctx.entries;
    env = var :: ctx.env;
    lvl = ctx.lvl + 1;
  }

let bind_def name ty value ctx =
  {
    entries = { name; ty } :: ctx.entries;
    env = value :: ctx.env;
    lvl = ctx.lvl + 1;
  }

let lookup_idx ctx (Idx.Idx k) =
  let e = List.nth ctx.entries k in
  e.ty

let lookup_name ctx name =
  let rec go k = function
    | [] -> None
    | { name = Some n; ty } :: _ when n = name -> Some (k, ty)
    | _ :: rest -> go (k + 1) rest
  in
  go 0 ctx.entries

let names ctx =
  List.map
    (fun e ->
      match e.name with
      | Some n -> n
      | None -> "_")
    ctx.entries
