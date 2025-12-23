open Syntax

exception Eval_error of string

let rec eval_ty (genv : Global.t) (env : env) : ty -> vl_ty = function
  | TyU -> VTyU
  | TyPi (x, a, b) -> VTyPi (x, eval_ty genv env a, ClosTy (env, b))
  | TyEl t -> do_el (eval_tm genv env t)

and do_el : vl_tm -> vl_ty = function
  | VTmPiHat (x, a, ClosTm (env', b)) ->
      VTyPi (x, do_el a, ClosTy (env', TyEl b))
  | VTmNeutral n -> VTyEl n
  | _ -> raise (Eval_error "do_el: expected type code or neutral")

and eval_tm (genv : Global.t) (env : env) : tm -> vl_tm = function
  | TmVar (Idx l) -> List.nth env l
  | TmConst name -> (
      match Global.find_tm name genv with
      | Some v -> v
      | None -> VTmNeutral (HConst name, []))
  | TmLam (x, a, body) -> VTmLam (x, eval_ty genv env a, ClosTm (env, body))
  | TmApp (f, a) -> do_app genv (eval_tm genv env f) (eval_tm genv env a)
  | TmPiHat (x, a, b) -> VTmPiHat (x, eval_tm genv env a, ClosTm (env, b))
  | TmSorry (id, ty) -> VTmNeutral (HSorry (id, eval_ty genv env ty), [])
  | TmLet (_, _, t, body) -> eval_tm genv (eval_tm genv env t :: env) body

and do_app (genv : Global.t) (f : vl_tm) (a : vl_tm) : vl_tm =
  match f with
  | VTmLam (_, _, ClosTm (env, body)) -> eval_tm genv (a :: env) body
  | VTmNeutral (h, sp) -> (
      let ne : neutral = (h, sp @ [ a ]) in
      match try_iota_reduce genv ne with
      | Some v -> v
      | None -> VTmNeutral ne)
  | _ -> raise (Eval_error "do_app: expected lambda or neutral")

and try_iota_reduce (genv : Global.t) : neutral -> vl_tm option = function
  | HConst rec_name, sp -> (
      match Global.find_recursor rec_name genv with
      | None -> None
      | Some info -> (
          let major_idx =
            info.rec_num_params + info.rec_num_motives + info.rec_num_methods
            + info.rec_num_indices
          in
          if List.length sp <= major_idx then
            None
          else
            let major = List.nth sp major_idx in
            match major with
            | VTmNeutral (HConst ctor_name, ctor_sp) -> (
                match
                  List.find_opt
                    (fun r -> r.Global.rule_ctor_name = ctor_name)
                    info.rec_rules
                with
                | None -> None
                | Some rule ->
                    let params = List.take info.rec_num_params sp in
                    let motive = List.nth sp info.rec_num_params in
                    let methods_start = info.rec_num_params + 1 in
                    let methods =
                      List.drop methods_start sp
                      |> List.take info.rec_num_methods
                    in
                    let fields = List.drop info.rec_num_params ctor_sp in
                    let method_idx =
                      List.find_index
                        (fun r -> r.Global.rule_ctor_name = ctor_name)
                        info.rec_rules
                      |> Option.get
                    in
                    let method_val = List.nth methods method_idx in
                    let app arg fn = do_app genv fn arg in
                    let apps args fn = List.fold_left (do_app genv) fn args in
                    let ihs =
                      List.mapi
                        (fun ih_idx rec_arg_idx ->
                          let field = List.nth fields rec_arg_idx in
                          let rec_indices_for_this =
                            List.nth rule.rule_rec_indices ih_idx
                          in
                          let field_indices =
                            List.map (List.nth fields) rec_indices_for_this
                          in
                          let rec_head =
                            VTmNeutral
                              (HConst (Name.child info.rec_ind_name "rec"), [])
                          in
                          rec_head |> apps params |> app motive |> apps methods
                          |> apps field_indices |> app field)
                        rule.rule_rec_args
                    in
                    Some (method_val |> apps fields |> apps ihs))
            | _ -> None))
  | _ -> None
