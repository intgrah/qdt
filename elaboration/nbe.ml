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

and try_iota_reduce (genv : Global.t) (ne : neutral) : vl_tm option =
  let ( let* ) = Option.bind in
  let* rec_name, sp =
    match ne with
    | HConst rec_name, sp -> Some (rec_name, sp)
    | _ -> None
  in
  let* info = Global.find_recursor rec_name genv in
  let major_idx =
    info.rec_num_params + 1 + info.rec_num_methods + info.rec_num_indices
  in
  let* major = List.nth_opt sp major_idx in
  let* ctor_name, ctor_sp =
    match major with
    | VTmNeutral (HConst ctor_name, ctor_sp) -> Some (ctor_name, ctor_sp)
    | _ -> None
  in

  let* rule =
    List.find_opt (fun r -> r.Global.rule_ctor_name = ctor_name) info.rec_rules
  in
  let params = List.take info.rec_num_params sp in
  let motive = List.nth sp info.rec_num_params in
  let methods =
    List.drop (info.rec_num_params + 1) sp |> List.take info.rec_num_methods
  in
  let fields = List.drop info.rec_num_params ctor_sp in
  let pattern_val = eval_tm genv [] rule.rule_rec_rhs in
  let rec apply_all_args f args =
    match args with
    | [] -> f
    | arg :: rest -> (
        match f with
        | VTmLam (_, _, ClosTm (env, body)) ->
            let new_env = arg :: env in
            let new_body_val = eval_tm genv new_env body in
            apply_all_args new_body_val rest
        | _ -> raise (Eval_error "Expected lambda when applying arguments"))
  in
  let all_args = params @ [ motive ] @ methods @ fields in
  Some (apply_all_args pattern_val all_args)

let rec conv_ty (genv : Global.t) (l : int) (ty1 : vl_ty) (ty2 : vl_ty) : bool =
  match (ty1, ty2) with
  | VTyU, VTyU -> true
  | VTyPi (_, a1, ClosTy (env1, b1)), VTyPi (_, a2, ClosTy (env2, b2)) ->
      conv_ty genv l a1 a2
      &&
      let var = VTmNeutral (HVar (Lvl l), []) in
      conv_ty genv (l + 1)
        (eval_ty genv (var :: env1) b1)
        (eval_ty genv (var :: env2) b2)
  | VTyEl n1, VTyEl n2 -> conv_neutral genv l (n1, n2)
  | _ -> false

and conv_tm (genv : Global.t) (l : int) (tm1 : vl_tm) (tm2 : vl_tm) : bool =
  match (tm1, tm2) with
  | VTmNeutral n1, VTmNeutral n2 ->
      conv_neutral genv l (n1, n2)
      || try_eta_struct genv l n1 (VTmNeutral n1)
      || try_eta_struct genv l n2 (VTmNeutral n2)
  | VTmLam (_, _, ClosTm (env1, body1)), VTmLam (_, _, ClosTm (env2, body2)) ->
      let var = VTmNeutral (HVar (Lvl l), []) in
      conv_tm genv (l + 1)
        (eval_tm genv (var :: env1) body1)
        (eval_tm genv (var :: env2) body2)
  | VTmPiHat (_, a1, ClosTm (env1, b1)), VTmPiHat (_, a2, ClosTm (env2, b2)) ->
      conv_tm genv l a1 a2
      &&
      let var = VTmNeutral (HVar (Lvl l), []) in
      conv_tm genv (l + 1)
        (eval_tm genv (var :: env1) b1)
        (eval_tm genv (var :: env2) b2)
  | _ -> false

and try_eta_struct (genv : Global.t) (l : int) (ctor_app : neutral)
    (other : vl_tm) : bool =
  match ctor_app with
  | HConst ctor_name, sp -> (
      match Global.find_constructor ctor_name genv with
      | None -> false
      | Some info -> (
          let info_opt : Global.structure_info option =
            match Global.find_structure info.ind_name genv with
            | Some info -> Some info
            | None -> (
                (* Also allow eta for unit-like types *)
                match
                  Global.find_recursor (Name.child info.ind_name "rec") genv
                with
                | Some rec_info
                  when rec_info.rec_num_indices = 0
                       && List.length rec_info.rec_rules = 1 ->
                    let rule = List.hd rec_info.rec_rules in
                    if rule.rule_nfields = 0 && rule.rule_ctor_name = ctor_name
                    then
                      Some
                        {
                          struct_ind_name = info.ind_name;
                          struct_ctor_name = ctor_name;
                          struct_num_params = rec_info.rec_num_params;
                          struct_num_fields = 0;
                          struct_field_names = [];
                        }
                    else
                      None
                | _ -> None)
          in
          match info_opt with
          | None -> false
          | Some info ->
              if
                List.length sp
                <> info.struct_num_params + info.struct_num_fields
              then
                false
              else
                let params = List.take info.struct_num_params sp in
                let fields = List.drop info.struct_num_params sp in
                List.for_all2
                  (fun fname field ->
                    let proj_name = Name.child info.struct_ind_name fname in
                    let proj_result =
                      match Global.find_tm proj_name genv with
                      | Some proj_fn ->
                          let with_params =
                            List.fold_left (do_app genv) proj_fn params
                          in
                          do_app genv with_params other
                      | None -> VTmNeutral (HConst proj_name, [])
                    in
                    conv_tm genv l field proj_result)
                  info.struct_field_names fields))
  | _, _ -> false

and conv_neutral (genv : Global.t) (l : int)
    (((h1, sp1), (h2, sp2)) : neutral * neutral) : bool =
  let head_eq =
    match (h1, h2) with
    | HVar l1, HVar l2 -> l1 = l2
    | HConst n1, HConst n2 -> n1 = n2
    | HSorry (id1, _), HSorry (id2, _) -> id1 = id2
    | _, _ -> false
  in
  head_eq && List.for_all2 (conv_tm genv l) sp1 sp2
