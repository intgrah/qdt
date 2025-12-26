open Syntax
open Frontend

let elab_params genv (params : Ast.typed_binder list) =
  let rec go ctx acc genv = function
    | [] -> (ctx, List.rev acc)
    | (_, name, ty) :: rest ->
        let ty = Bidir.check_ty genv ctx ty in
        let ty_val = Nbe.eval_ty genv ctx.env ty in
        let ctx = Context.bind name ty_val ctx in
        go ctx ((name, ty) :: acc) genv rest
  in
  go Context.empty [] genv params

let build_pi =
  List.fold_right (fun (name, param_ty) body -> TyPi (name, param_ty, body))

let build_lambda =
  List.fold_right (fun (name, param_ty) body -> TmLam (name, param_ty, body))
