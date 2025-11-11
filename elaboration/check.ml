open Syntax

(* Type checking context *)
type context = {
  env : env;
  lvl : lvl;
  types : val_ty list;
  bds : bd list; (* Bound vs Defined tracking *)
}

let empty_context : context = { env = []; lvl = 0; types = []; bds = [] }

let bind_var (ctx : context) (ty : val_ty) : context =
  let var = VRigid (ctx.lvl, []) in
  {
    env = var :: ctx.env;
    lvl = ctx.lvl + 1;
    types = ty :: ctx.types;
    bds = Bound :: ctx.bds;
  }

(* Bind a let-definition - metas cannot abstract over these *)
let bind_def (ctx : context) (v : val_ty) (ty : val_ty) : context =
  {
    env = v :: ctx.env;
    lvl = ctx.lvl + 1;
    types = ty :: ctx.types;
    bds = Defined :: ctx.bds;
  }
