open Frontend
open Syntax

(* ========== Raw Syntax ========== *)

let pp_list pp_item = Format.pp_print_list ~pp_sep:Format.pp_print_space pp_item

let rec pp_name fmt : string option -> unit = function
  | None -> Format.fprintf fmt "_"
  | Some name -> Format.fprintf fmt "%s" name

and pp_typed_binder_group fmt ((names, ty) : Raw_syntax.typed_binder_group) :
    unit =
  Format.fprintf fmt "(%a : %a)" (pp_list pp_name) names pp_raw ty

and pp_binder_group fmt : Raw_syntax.binder_group -> unit = function
  | Raw_syntax.Untyped name -> Format.fprintf fmt "%s" name
  | Raw_syntax.Typed group -> pp_typed_binder_group fmt group

and pp_raw fmt : Raw_syntax.t -> unit = function
  | Ident name -> Format.fprintf fmt "%s" name
  | App (f, a) -> Format.fprintf fmt "@[<hov 2>(%a@ %a)@]" pp_raw f pp_raw a
  | Lam (binders, body) ->
      Format.fprintf fmt "@[<hov 2>(fun %a =>@ %a)@]" (pp_list pp_binder_group)
        binders pp_raw body
  | Pi (group, b) ->
      Format.fprintf fmt "@[<hov>%a →@ %a@]" pp_typed_binder_group group pp_raw
        b
  | Arrow (a, b) -> Format.fprintf fmt "@[<hov 2>%a →@ %a@]" pp_raw a pp_raw b
  | Let (name, None, rhs, body) ->
      Format.fprintf fmt "@[<v 0>@[<hov 2>(let %s :=@ %a in@]@ %a)@]" name
        pp_raw rhs pp_raw body
  | Let (name, Some ty, rhs, body) ->
      Format.fprintf fmt "@[<v 0>@[<hov 2>(let %s : %a :=@ %a in@]@ %a)@]" name
        pp_raw ty pp_raw rhs pp_raw body
  | U -> Format.fprintf fmt "Type"
  | Eq (a, b) -> Format.fprintf fmt "@[<hov 2>%a@ = %a@]" pp_raw a pp_raw b
  | Pair (a, b) -> Format.fprintf fmt "@[<hov 2>(%a,@ %a)@]" pp_raw a pp_raw b
  | Sigma (group, b) ->
      Format.fprintf fmt "@[<hov 2>%a@ × %a@]" pp_typed_binder_group group
        pp_raw b
  | Prod (a, b) -> Format.fprintf fmt "@[<hov 2>%a@ × %a@]" pp_raw a pp_raw b
  | NatLit n -> Format.fprintf fmt "%d" n
  | Add (a, b) -> Format.fprintf fmt "@[<hov 2>%a@ + %a@]" pp_raw a pp_raw b
  | Sub (a, b) -> Format.fprintf fmt "@[<hov 2>%a@ - %a@]" pp_raw a pp_raw b
  | Ann (e, ty) -> Format.fprintf fmt "@[<hov 2>(%a@ : %a)@]" pp_raw e pp_raw ty
  | Sorry -> Format.fprintf fmt "sorry"

let pp_ctor fmt (ctor : Raw_syntax.constructor) : unit =
  match (ctor.params, ctor.ty_opt) with
  | [], None -> Format.fprintf fmt "| %s" ctor.name
  | [], Some ty -> Format.fprintf fmt "| %s : %a" ctor.name pp_raw ty
  | params, None ->
      Format.fprintf fmt "| %s %a" ctor.name
        (pp_list pp_typed_binder_group)
        params
  | params, Some ty ->
      Format.fprintf fmt "| %s %a : %a" ctor.name
        (pp_list pp_typed_binder_group)
        params pp_raw ty

let pp_raw_item fmt : Raw_syntax.item -> unit = function
  | Def { name; params; ty_opt; body } -> (
      let pp_params fmt params =
        if params <> [] then
          Format.fprintf fmt " %a" (pp_list pp_typed_binder_group) params
      in
      match ty_opt with
      | Some ty ->
          Format.fprintf fmt "@[<hov 2>def %s%a : %a :=@ %a@]" name pp_params
            params pp_raw ty pp_raw body
      | None ->
          Format.fprintf fmt "@[<hov 2>def %s%a :=@ %a@]" name pp_params params
            pp_raw body)
  | Example { params; ty_opt; body } -> (
      let pp_params fmt params =
        if params <> [] then
          Format.fprintf fmt " %a" (pp_list pp_typed_binder_group) params
      in
      match ty_opt with
      | Some ty ->
          Format.fprintf fmt "@[<hov 2>example%a : %a :=@ %a@]" pp_params params
            pp_raw ty pp_raw body
      | None ->
          Format.fprintf fmt "@[<hov 2>example%a :=@ %a@]" pp_params params
            pp_raw body)
  | Axiom { name; params; ty } ->
      let pp_params fmt params =
        if params <> [] then
          Format.fprintf fmt " %a" (pp_list pp_typed_binder_group) params
      in
      Format.fprintf fmt "@[<hov 2>axiom %s%a : %a@]" name pp_params params
        pp_raw ty
  | Inductive { name; params; ty_opt; ctors } -> (
      let pp_params fmt params =
        if params <> [] then
          Format.fprintf fmt " %a" (pp_list pp_typed_binder_group) params
      in
      match ty_opt with
      | None ->
          Format.fprintf fmt "@[<v 0>inductive %s%a where@,%a@]" name pp_params
            params
            (Format.pp_print_list ~pp_sep:Format.pp_print_cut pp_ctor)
            ctors
      | Some ty ->
          Format.fprintf fmt "@[<v 0>inductive %s%a : %a where@,%a@]" name
            pp_params params pp_raw ty
            (Format.pp_print_list ~pp_sep:Format.pp_print_cut pp_ctor)
            ctors)
  | Structure { name; params; ty_opt; fields } -> (
      let pp_params fmt params =
        if params <> [] then
          Format.fprintf fmt " %a" (pp_list pp_typed_binder_group) params
      in
      let pp_field fmt (field : Raw_syntax.field) =
        match field.binders with
        | [] -> Format.fprintf fmt "(%s : %a)" field.name pp_raw field.ty
        | args ->
            Format.fprintf fmt "(%s %a : %a)" field.name
              (pp_list pp_typed_binder_group)
              args pp_raw field.ty
      in
      match ty_opt with
      | None ->
          Format.fprintf fmt "@[<v 0>structure %s%a where@,%a@]" name pp_params
            params
            (Format.pp_print_list ~pp_sep:Format.pp_print_cut pp_field)
            fields
      | Some ty ->
          Format.fprintf fmt "@[<v 0>structure %s%a : %a where@,%a@]" name
            pp_params params pp_raw ty
            (Format.pp_print_list ~pp_sep:Format.pp_print_cut pp_field)
            fields)
  | Import { module_name } -> Format.fprintf fmt "import %s" module_name

let pp_raw_program fmt (prog : Raw_syntax.program) : unit =
  Format.pp_print_list
    ~pp_sep:(fun fmt () -> Format.fprintf fmt "\n\n")
    pp_raw_item fmt prog

(* ========== Core Syntax ========== *)

let fresh_name (names : string list) : string =
  let rec go i =
    let candidate = Format.sprintf "x%d†" i in
    if List.mem candidate names then
      go (i + 1)
    else
      candidate
  in
  go 0

let get_name (name_opt : string option) (names : string list) : string =
  match name_opt with
  | Some name -> name
  | None -> fresh_name names

let parens_if cond fmt (pp : Format.formatter -> unit) =
  if cond then
    Format.fprintf fmt "(@[%t@])" pp
  else
    pp fmt

(* Precedence levels: lower = looser binding *)
let prec_let = 0
let prec_pi = 1
let prec_fun = 1
let prec_app = 3
let prec_atom = 4

let rec pp_ty_prec (names : string list) (ctx_prec : int) fmt : ty -> unit =
  function
  | TyU -> Format.fprintf fmt "Type"
  | TyPi (None, a, b) ->
      let my_prec = prec_pi in
      let pp fmt =
        Format.fprintf fmt "@[<hv 0>%a@]@ →@ @[<hv 0>%a@]"
          (pp_ty_prec names prec_pi) a
          (pp_ty_prec (fresh_name names :: names) prec_pi)
          b
      in
      parens_if (ctx_prec > my_prec) fmt pp
  | TyPi (Some x, a, b) ->
      let my_prec = prec_pi in
      let pp fmt =
        Format.fprintf fmt "@[<hov 0>(%s :@;<1 2>%a) →@ %a@]" x
          (pp_ty_prec names prec_fun)
          a
          (pp_ty_prec (x :: names) prec_pi)
          b
      in
      parens_if (ctx_prec > my_prec) fmt pp
  | TyEl (TmApp (TmApp (TmConst [ "Prod" ], a_code), b_code)) ->
      let my_prec = prec_pi in
      let pp fmt =
        Format.fprintf fmt "@[<hov 2>%a@ × %a@]"
          (pp_ty_prec names prec_app)
          (TyEl a_code) (pp_ty_prec names prec_pi) (TyEl b_code)
      in
      parens_if (ctx_prec > my_prec) fmt pp
  | TyEl (TmApp (TmApp (TmConst [ "Sigma" ], _), TmLam (x_opt, x_ty, b_code)))
    ->
      let x = get_name x_opt names in
      let my_prec = prec_pi in
      let pp fmt =
        Format.fprintf fmt "@[<hov 0>(%s :@;<1 2>%a) × %a@]" x
          (pp_ty_prec names prec_fun)
          x_ty
          (pp_ty_prec (x :: names) prec_pi)
          (TyEl b_code)
      in
      parens_if (ctx_prec > my_prec) fmt pp
  | TyEl t -> Format.fprintf fmt "%a" (pp_tm_prec names ctx_prec) t

and pp_tm_prec (names : string list) (ctx_prec : int) fmt : tm -> unit =
  let rec flatten_app acc = function
    | TmApp (f, a) -> flatten_app (a :: acc) f
    | head -> (head, acc)
  in
  function
  | TmVar (Idx l) ->
      let nm =
        if l < List.length names then
          List.nth names l
        else
          Format.sprintf "x%d†" l
      in
      Format.fprintf fmt "%s" nm
  | TmConst name -> Format.fprintf fmt "%a" Name.pp name
  | TmLam (name_opt, a, body) ->
      let my_prec = prec_fun in
      let x = get_name name_opt names in
      let pp fmt =
        Format.fprintf fmt "@[<hov 2>fun %s : %a =>@ %a@]" x
          (pp_ty_prec names prec_fun)
          a
          (pp_tm_prec (x :: names) prec_fun)
          body
      in
      parens_if (ctx_prec > my_prec) fmt pp
  | TmPiHat (None, a, b) ->
      let my_prec = prec_pi in
      let pp fmt =
        Format.fprintf fmt "@[<hov>%a →@ %a@]" (pp_tm_prec names prec_pi) a
          (pp_tm_prec (fresh_name names :: names) prec_pi)
          b
      in
      parens_if (ctx_prec > my_prec) fmt pp
  | TmPiHat (Some x, a, b) ->
      let my_prec = prec_pi in
      let pp fmt =
        Format.fprintf fmt "@[<hov 0>(%s :@;<1 2>%a) →@ %a@]" x
          (pp_tm_prec names prec_fun)
          a
          (pp_tm_prec (x :: names) prec_pi)
          b
      in
      parens_if (ctx_prec > my_prec) fmt pp
  | TmSorry _ -> Format.fprintf fmt "sorry"
  | TmLet (x, ty, t, body) ->
      let my_prec = prec_let in
      let pp fmt =
        Format.fprintf fmt "@[<v 0>@[<hov 2>let %s : %a :=@ %a;@]@ %a@]" x
          (pp_ty_prec names prec_fun)
          ty
          (pp_tm_prec names prec_let)
          t
          (pp_tm_prec (x :: names) prec_let)
          body
      in
      parens_if (ctx_prec > my_prec) fmt pp
  | tm ->
      (* application or atom *)
      let head, args = flatten_app [] tm in
      let my_prec = prec_app in
      let pp fmt =
        let pp_head fmt = pp_tm_prec names my_prec fmt head in
        let pp_args fmt = pp_list (pp_tm_prec names prec_atom) fmt args in
        Format.fprintf fmt "@[<hov 2>%t@ %t@]" pp_head pp_args
      in
      parens_if (ctx_prec > my_prec) fmt pp

let pp_ty_ctx names fmt ty = pp_ty_prec names prec_let fmt ty
let pp_ty = pp_ty_prec [] prec_let
let pp_tm = pp_tm_prec [] prec_let

let pp_def fmt ((name, term, ty) : Name.t * tm * ty) : unit =
  Format.fprintf fmt "@[<v 0>def %a :@;<0 4>%a@;<0 4>:= %a@]" Name.pp name pp_ty
    ty pp_tm term

(* ========== Values ========== *)

let env_names (env : env) : string list =
  List.init (List.length env) (Format.sprintf "env%d†")

let rec pp_vl_ty_ctx (names : string list) fmt : vl_ty -> unit = function
  | VTyU -> Format.fprintf fmt "Type"
  | VTyPi (None, a, clos) ->
      let x = fresh_name names in
      Format.fprintf fmt "@[<hov 2>%a →@ %a@]" (pp_vl_ty_ctx names) a
        (pp_clos_ty x) clos
  | VTyPi (Some x, a, clos) ->
      let x = get_name (Some x) names in
      Format.fprintf fmt "@[<hov 2>(%s : %a) →@ %a@]" x (pp_vl_ty_ctx names) a
        (pp_clos_ty x) clos
  | VTyEl n -> pp_neutral_ctx names fmt n

and pp_vl_tm_ctx (names : string list) fmt : vl_tm -> unit = function
  | VTmNeutral n -> pp_neutral_ctx names fmt n
  | VTmLam (x_opt, a, clos) ->
      let x = get_name x_opt names in
      Format.fprintf fmt "@[<hov 2>(fun %s : %a =>@ %a)@]" x
        (pp_vl_ty_ctx names) a (pp_clos_tm x) clos
  | VTmPiHat (None, a, clos) ->
      let x = fresh_name names in
      Format.fprintf fmt "@[<hov 2>%a →@ %a@]" (pp_vl_tm_ctx names) a
        (pp_clos_tm x) clos
  | VTmPiHat (Some x, a, clos) ->
      let x = get_name (Some x) names in
      Format.fprintf fmt "@[<hov 2>(%s : %a) →@ %a@]" x (pp_vl_tm_ctx names) a
        (pp_clos_tm x) clos

and pp_neutral_ctx (names : string list) fmt ((head, sp) : neutral) : unit =
  match sp with
  | [] -> pp_head fmt head
  | _ ->
      Format.fprintf fmt "@[<hov 2>(%a@ %a)@]" pp_head head
        (pp_list (pp_vl_tm_ctx names))
        sp

and pp_head fmt : head -> unit = function
  | HVar lvl -> Format.fprintf fmt "x%d†" (Lvl.to_int lvl)
  | HConst name -> Format.fprintf fmt "%a" Name.pp name
  | HSorry (id, _ty) -> Format.fprintf fmt "sorry%d" id

and pp_clos_ty (x : string) fmt : clos_ty -> unit = function
  | ClosTy (env, body) -> pp_ty_prec (x :: env_names env) prec_let fmt body

and pp_clos_tm (x : string) fmt : clos_tm -> unit = function
  | ClosTm (env, body) -> pp_tm_prec (x :: env_names env) prec_let fmt body

let pp_vl_ty fmt (ty : vl_ty) : unit = pp_vl_ty_ctx [] fmt ty
let pp_vl_tm fmt (tm : vl_tm) : unit = pp_vl_tm_ctx [] fmt tm
