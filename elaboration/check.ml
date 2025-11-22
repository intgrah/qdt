open Syntax

(* Type checking context *)
type context = {
  env : env;
  lvl : lvl;
  types : vl list;
  bds : bd list; (* Bound vs Defined tracking *)
}

let empty_context : context = { env = []; lvl = 0; types = []; bds = [] }

let bind_var (ctx : context) (ty : vl) : context =
  let var = VRigid (ctx.lvl, []) in
  {
    env = var :: ctx.env;
    lvl = ctx.lvl + 1;
    types = ty :: ctx.types;
    bds = Bound :: ctx.bds;
  }

let bind_def (ctx : context) (v : vl) (ty : vl) : context =
  {
    env = v :: ctx.env;
    lvl = ctx.lvl + 1;
    types = ty :: ctx.types;
    bds = Defined :: ctx.bds;
  }
