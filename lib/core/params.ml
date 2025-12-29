open Frontend

let elab_params_from :
    Context.t ->
    Global.t ->
    Ast.typed_binder list ->
    Context.t * (string option * Syntax.ty) list =
  let rec go acc ctx genv = function
    | [] -> (ctx, List.rev acc)
    | (_, name, ty) :: rest ->
        let ty = Bidir.check_ty genv ctx ty in
        let ty_val = Nbe.eval_ty genv ctx.env ty in
        let ctx = Context.bind name ty_val ctx in
        go ((name, ty) :: acc) ctx genv rest
  in
  go []

let elab_params = elab_params_from Context.empty
