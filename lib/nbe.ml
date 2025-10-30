open Core

let rec apply_spine (v : tm_value) : spine -> tm_value = function
  | [] -> v
  | FApp arg :: rest ->
      let v' = apply v arg in
      apply_spine v' rest

and apply (f : tm_value) (arg : tm_value) : tm_value =
  match f with
  | LambdaV (_, (env, body)) -> eval (arg :: env) body
  | Neutral (h, sp, bnd) -> Neutral (h, sp @ [ FApp arg ], bnd)

and eval (env : env) : tm -> tm_value = function
  | Var n -> ( try List.nth env n with _ -> failwith "variable out of scope")
  | Lambda body ->
      let ty = StarV in
      LambdaV (ty, (env, body))
  | App (f, a) ->
      let fv = eval env f in
      let av = eval env a in
      apply fv av

let rec eval_ty (env : env) : ty -> ty_value = function
  | TVar _n -> failwith "type variables not yet supported"
  | Pi (a, b) -> PiV (eval_ty env a, (env, b))
  | Star -> StarV

let instantiate (ty_clos : ty_closure) (arg : tm_value) : ty_value =
  let env, body = ty_clos in
  eval_ty (arg :: env) body

let fresh_var = ref 0

let gen_fresh () =
  let v = !fresh_var in
  fresh_var := v + 1;
  v

let rec quote_spine (acc : tm) (lvl : int) : spine -> tm = function
  | [] -> acc
  | FApp arg :: rest ->
      let arg_tm = quote arg lvl in
      let app_tm = App (acc, arg_tm) in
      quote_spine app_tm lvl rest

and quote (v : tm_value) (lvl : int) : tm =
  match v with
  | LambdaV (ty, clos) ->
      let var_neutral = Neutral (Local lvl, [], lazy (Abstract ty)) in
      let body_val = eval (var_neutral :: fst clos) (snd clos) in
      let body = quote body_val (lvl + 1) in
      Core.Lambda body
  | Neutral (h, sp, _) ->
      let h_tm = quote_head lvl h in
      quote_spine h_tm lvl sp

and quote_head (lvl : int) (h : head) : tm =
  match h with
  | Local n -> Core.Var (lvl - n - 1)
  | Global _name -> failwith "global not yet supported"

let rec quote_ty (lvl : int) (v : ty_value) : ty =
  match v with
  | StarV -> Star
  | PiV (a, ty_clos) ->
      let a_ty = quote_ty lvl a in
      let var_neutral = Neutral (Local lvl, [], lazy (Abstract a)) in
      let b = instantiate ty_clos var_neutral in
      let b_ty = quote_ty (lvl + 1) b in
      Pi (a_ty, b_ty)

let rec conv (v1 : tm_value) (v2 : tm_value) (lvl : int) : bool =
  let t1 = quote v1 lvl in
  let t2 = quote v2 lvl in
  tm_eq t1 t2

and tm_eq (t1 : tm) (t2 : tm) : bool =
  match (t1, t2) with
  | Var n1, Var n2 -> n1 = n2
  | Lambda b1, Lambda b2 -> tm_eq b1 b2
  | App (f1, a1), App (f2, a2) -> tm_eq f1 f2 && tm_eq a1 a2
  | _ -> false

let rec conv_ty (v1 : ty_value) (v2 : ty_value) (lvl : int) : bool =
  let t1 = quote_ty lvl v1 in
  let t2 = quote_ty lvl v2 in
  ty_eq t1 t2

and ty_eq (t1 : ty) (t2 : ty) : bool =
  match (t1, t2) with
  | TVar n1, TVar n2 -> n1 = n2
  | Pi (a1, b1), Pi (a2, b2) -> ty_eq a1 a2 && ty_eq b1 b2
  | Star, Star -> true
  | _ -> false
