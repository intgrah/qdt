open Syntax
open Semantics
open Frontend
open Parser

let pp_list pp_item = Format.pp_print_list ~pp_sep:Format.pp_print_space pp_item

let rec pp_name fmt name : unit =
  Format.fprintf fmt "%s" (Option.value name ~default:"_")

and pp_typed_binder_group fmt ((_, names, ty) : Cst.typed_binder_group) : unit =
  Format.fprintf fmt "(%a : %a)" (pp_list pp_name) names pp_cst ty

and pp_binder_group fmt : Cst.binder_group -> unit = function
  | Untyped (_, name) -> pp_name fmt name
  | Typed group -> pp_typed_binder_group fmt group

and pp_cst fmt : Cst.t -> unit = function
  | Missing _ -> Format.fprintf fmt "<missing>"
  | Ident (_, name) -> Format.fprintf fmt "%s" name
  | App (_, f, a) -> Format.fprintf fmt "@[<hov 2>(%a@ %a)@]" pp_cst f pp_cst a
  | Lam (_, binders, body) ->
      Format.fprintf fmt "@[<hov 2>(fun %a =>@ %a)@]" (pp_list pp_binder_group)
        binders pp_cst body
  | Pi (_, group, b) ->
      Format.fprintf fmt "@[<hov>%a →@ %a@]" pp_typed_binder_group group pp_cst
        b
  | Arrow (_, a, b) ->
      Format.fprintf fmt "@[<hov 2>%a →@ %a@]" pp_cst a pp_cst b
  | Let (_, name, None, rhs, body) ->
      Format.fprintf fmt "@[<v 0>@[<hov 2>(let %s :=@ %a in@]@ %a)@]" name
        pp_cst rhs pp_cst body
  | Let (_, name, Some ty, rhs, body) ->
      Format.fprintf fmt "@[<v 0>@[<hov 2>(let %s : %a :=@ %a in@]@ %a)@]" name
        pp_cst ty pp_cst rhs pp_cst body
  | U _ -> Format.fprintf fmt "Type"
  | Eq (_, a, b) -> Format.fprintf fmt "@[<hov 2>%a@ = %a@]" pp_cst a pp_cst b
  | Pair (_, a, b) ->
      Format.fprintf fmt "@[<hov 2>(%a,@ %a)@]" pp_cst a pp_cst b
  | Sigma (_, group, b) ->
      Format.fprintf fmt "@[<hov 2>%a@ × %a@]" pp_typed_binder_group group
        pp_cst b
  | Prod (_, a, b) -> Format.fprintf fmt "@[<hov 2>%a@ × %a@]" pp_cst a pp_cst b
  | NatLit (_, n) -> Format.fprintf fmt "%d" n
  | Add (_, a, b) -> Format.fprintf fmt "@[<hov 2>%a@ + %a@]" pp_cst a pp_cst b
  | Sub (_, a, b) -> Format.fprintf fmt "@[<hov 2>%a@ - %a@]" pp_cst a pp_cst b
  | Mul (_, a, b) -> Format.fprintf fmt "@[<hov 2>%a@ * %a@]" pp_cst a pp_cst b
  | Ann (_, e, ty) ->
      Format.fprintf fmt "@[<hov 2>(%a@ : %a)@]" pp_cst e pp_cst ty
  | Sorry _ -> Format.fprintf fmt "sorry"

let pp_ctor fmt (ctor : Cst.Command.inductive_constructor) : unit =
  match (ctor.params, ctor.ty_opt) with
  | [], None -> Format.fprintf fmt "| %s" ctor.name
  | [], Some ty -> Format.fprintf fmt "| %s : %a" ctor.name pp_cst ty
  | params, None ->
      Format.fprintf fmt "| %s %a" ctor.name
        (pp_list pp_typed_binder_group)
        params
  | params, Some ty ->
      Format.fprintf fmt "| %s %a : %a" ctor.name
        (pp_list pp_typed_binder_group)
        params pp_cst ty

let pp_cst_params fmt params =
  if params <> [] then
    Format.fprintf fmt " %a" (pp_list pp_typed_binder_group) params

let pp_cst_command fmt : Cst.Command.t -> unit = function
  | Definition { src = _; name; params; ty_opt; body } -> (
      match ty_opt with
      | Some ty ->
          Format.fprintf fmt "@[<hov 2>def %s%a : %a :=@ %a@]" name
            pp_cst_params params pp_cst ty pp_cst body
      | None ->
          Format.fprintf fmt "@[<hov 2>def %s%a :=@ %a@]" name pp_cst_params
            params pp_cst body)
  | Example { src = _; params; ty_opt; body } -> (
      match ty_opt with
      | Some ty ->
          Format.fprintf fmt "@[<hov 2>example%a : %a :=@ %a@]" pp_cst_params
            params pp_cst ty pp_cst body
      | None ->
          Format.fprintf fmt "@[<hov 2>example%a :=@ %a@]" pp_cst_params params
            pp_cst body)
  | Axiom { src = _; name; params; ty } ->
      Format.fprintf fmt "@[<hov 2>axiom %s%a : %a@]" name pp_cst_params params
        pp_cst ty
  | Inductive { src = _; name; params; ty_opt; ctors } -> (
      match ty_opt with
      | None ->
          Format.fprintf fmt "@[<v 0>inductive %s%a where@,%a@]" name
            pp_cst_params params
            (Format.pp_print_list ~pp_sep:Format.pp_print_cut pp_ctor)
            ctors
      | Some ty ->
          Format.fprintf fmt "@[<v 0>inductive %s%a : %a where@,%a@]" name
            pp_cst_params params pp_cst ty
            (Format.pp_print_list ~pp_sep:Format.pp_print_cut pp_ctor)
            ctors)
  | Structure { src = _; name; params; ty_opt; fields } -> (
      let pp_field fmt (field : Cst.Command.structure_field) =
        match field.params with
        | [] -> Format.fprintf fmt "(%s : %a)" field.name pp_cst field.ty
        | args ->
            Format.fprintf fmt "(%s %a : %a)" field.name
              (pp_list pp_typed_binder_group)
              args pp_cst field.ty
      in
      match ty_opt with
      | None ->
          Format.fprintf fmt "@[<v 0>structure %s%a where@,%a@]" name
            pp_cst_params params
            (Format.pp_print_list ~pp_sep:Format.pp_print_cut pp_field)
            fields
      | Some ty ->
          Format.fprintf fmt "@[<v 0>structure %s%a : %a where@,%a@]" name
            pp_cst_params params pp_cst ty
            (Format.pp_print_list ~pp_sep:Format.pp_print_cut pp_field)
            fields)
  | Import { src = _; module_name } ->
      Format.fprintf fmt "import %s" module_name

let pp_cst_program fmt (prog : Cst.program) : unit =
  Format.pp_print_list
    ~pp_sep:(fun fmt () -> Format.fprintf fmt "\n\n")
    pp_cst_command fmt prog

(* ========== Abstract Syntax ========== *)

let needs_parens (parent_prec : prec) (child_prec : prec) : bool =
  compare_prec parent_prec child_prec > 0

let rec pp_ast_prec (parent_prec : prec) fmt : Ast.t -> unit = function
  | Missing _ -> Format.fprintf fmt "<missing>"
  | Ident (_, name) -> Format.fprintf fmt "%s" name
  | App (_, f, a) ->
      let prec = PrecApp in
      let pp_f = pp_ast_prec prec in
      let pp_a = pp_ast_prec prec in
      if needs_parens parent_prec prec then
        Format.fprintf fmt "@[<hov 2>(%a@ %a)@]" pp_f f pp_a a
      else
        Format.fprintf fmt "@[<hov 2>%a@ %a@]" pp_f f pp_a a
  | Lam (_, binder, body) ->
      let prec = PrecFun in
      let pp_binder fmt = function
        | Ast.Untyped (_, name) -> pp_name fmt name
        | Ast.Typed (_, name, ty) ->
            Format.fprintf fmt "(%a : %a)" pp_name name (pp_ast_prec PrecMin) ty
      in
      let pp_body = pp_ast_prec prec in
      if needs_parens parent_prec prec then
        Format.fprintf fmt "@[<hov 2>(fun %a =>@ %a)@]" pp_binder binder pp_body
          body
      else
        Format.fprintf fmt "@[<hov 2>fun %a =>@ %a@]" pp_binder binder pp_body
          body
  | Pi (_, (_, name, ty), body) ->
      let prec = PrecPi in
      let pp_ty = pp_ast_prec PrecMin in
      let pp_body = pp_ast_prec prec in
      if needs_parens parent_prec prec then
        Format.fprintf fmt "@[<hov>(%a : %a) →@ %a@]" pp_name name pp_ty ty
          pp_body body
      else
        Format.fprintf fmt "@[<hov>%a : %a →@ %a@]" pp_name name pp_ty ty
          pp_body body
  | Let (_, name, None, rhs, body) ->
      let prec = PrecLet in
      Format.fprintf fmt "@[<v 0>@[<hov 2>let %s :=@ %a in@]@ %a@]" name
        (pp_ast_prec prec) rhs (pp_ast_prec prec) body
  | Let (_, name, Some ty, rhs, body) ->
      let prec = PrecLet in
      Format.fprintf fmt "@[<v 0>@[<hov 2>let %s : %a :=@ %a in@]@ %a@]" name
        (pp_ast_prec PrecMin) ty (pp_ast_prec prec) rhs (pp_ast_prec prec) body
  | U _ -> Format.fprintf fmt "Type"
  | Eq (_, a, b) ->
      let prec = PrecEq in
      let pp_a = pp_ast_prec prec in
      let pp_b = pp_ast_prec prec in
      if needs_parens parent_prec prec then
        Format.fprintf fmt "@[<hov 2>(%a@ = %a)@]" pp_a a pp_b b
      else
        Format.fprintf fmt "@[<hov 2>%a@ = %a@]" pp_a a pp_b b
  | Pair (_, a, b) ->
      Format.fprintf fmt "@[<hov 2>(%a,@ %a)@]" (pp_ast_prec PrecMin) a
        (pp_ast_prec PrecMin) b
  | Ann (_, e, ty) ->
      Format.fprintf fmt "@[<hov 2>(%a@ : %a)@]" (pp_ast_prec PrecMin) e
        (pp_ast_prec PrecMin) ty
  | Sorry _ -> Format.fprintf fmt "sorry"

let pp_ast fmt (t : Ast.t) = pp_ast_prec PrecMin fmt t

let pp_ast_typed_binder fmt (_, name, ty) =
  Format.fprintf fmt "(%a : %a)" pp_name name pp_ast ty

let pp_ast_params fmt params =
  if params <> [] then
    Format.fprintf fmt " %a"
      (Format.pp_print_list ~pp_sep:Format.pp_print_space pp_ast_typed_binder)
      params

let pp_ast_command fmt : Ast.Command.t -> unit = function
  | Import { src = _; module_name } ->
      Format.fprintf fmt "import %s" module_name
  | Definition { src = _; name; params; ty_opt; body } -> (
      match ty_opt with
      | Some ty ->
          Format.fprintf fmt "@[<hov 2>def %s%a : %a :=@ %a@]" name
            pp_ast_params params pp_ast ty pp_ast body
      | None ->
          Format.fprintf fmt "@[<hov 2>def %s%a :=@ %a@]" name pp_ast_params
            params pp_ast body)
  | Example { src = _; params; ty_opt; body } -> (
      match ty_opt with
      | Some ty ->
          Format.fprintf fmt "@[<hov 2>example%a : %a :=@ %a@]" pp_ast_params
            params pp_ast ty pp_ast body
      | None ->
          Format.fprintf fmt "@[<hov 2>example%a :=@ %a@]" pp_ast_params params
            pp_ast body)
  | Axiom { src = _; name; params; ty } ->
      Format.fprintf fmt "@[<hov 2>axiom %s%a : %a@]" name pp_ast_params params
        pp_ast ty
  | Inductive { src = _; name; params; ty_opt; ctors } -> (
      let pp_ctor fmt (ctor : Ast.Command.inductive_constructor) =
        match (ctor.params, ctor.ty_opt) with
        | [], None -> Format.fprintf fmt "| %s" ctor.name
        | [], Some ty -> Format.fprintf fmt "| %s : %a" ctor.name pp_ast ty
        | params, None ->
            Format.fprintf fmt "| %s %a" ctor.name
              (Format.pp_print_list ~pp_sep:Format.pp_print_space
                 pp_ast_typed_binder)
              params
        | params, Some ty ->
            Format.fprintf fmt "| %s %a : %a" ctor.name
              (Format.pp_print_list ~pp_sep:Format.pp_print_space
                 pp_ast_typed_binder)
              params pp_ast ty
      in
      match ty_opt with
      | None ->
          Format.fprintf fmt "@[<v 0>inductive %s%a where@,%a@]" name
            pp_ast_params params
            (Format.pp_print_list ~pp_sep:Format.pp_print_cut pp_ctor)
            ctors
      | Some ty ->
          Format.fprintf fmt "@[<v 0>inductive %s%a : %a where@,%a@]" name
            pp_ast_params params pp_ast ty
            (Format.pp_print_list ~pp_sep:Format.pp_print_cut pp_ctor)
            ctors)
  | Structure { src = _; name; params; ty_opt; fields } -> (
      let pp_field fmt (field : Ast.Command.structure_field) =
        match field.params with
        | [] -> Format.fprintf fmt "(%s : %a)" field.name pp_ast field.ty
        | args ->
            Format.fprintf fmt "(%s %a : %a)" field.name
              (Format.pp_print_list ~pp_sep:Format.pp_print_space
                 pp_ast_typed_binder)
              args pp_ast field.ty
      in
      match ty_opt with
      | None ->
          Format.fprintf fmt "@[<v 0>structure %s%a where@,%a@]" name
            pp_ast_params params
            (Format.pp_print_list ~pp_sep:Format.pp_print_cut pp_field)
            fields
      | Some ty ->
          Format.fprintf fmt "@[<v 0>structure %s%a : %a where@,%a@]" name
            pp_ast_params params pp_ast ty
            (Format.pp_print_list ~pp_sep:Format.pp_print_cut pp_field)
            fields)

let pp_ast_program : Format.formatter -> Ast.program -> unit =
  Format.pp_print_list
    ~pp_sep:(fun fmt () -> Format.fprintf fmt "@.@.")
    pp_ast_command

(* ========== Core Syntax ========== *)

let fresh_name (names : string option list) : string =
  let rec go i =
    let candidate = Format.sprintf "x%d" i in
    if
      List.exists
        (function
          | Some n -> n = candidate
          | None -> false)
        names
    then
      go (i + 1)
    else
      candidate
  in
  go 0

let get_name_for_binding (name : string option) (names : string option list) :
    string =
  match name with
  | Some name -> name
  | None -> fresh_name names

let parens_if cond fmt (pp : Format.formatter -> unit) =
  if cond then
    Format.fprintf fmt "(@[%t@])" pp
  else
    pp fmt

let rec pp_ty_prec (ctx_prec : prec) (names : string option list) fmt :
    ty -> unit = function
  | TyU -> Format.fprintf fmt "Type"
  | TyPi (None, a, b) ->
      let my_prec = PrecPi in
      let pp fmt =
        Format.fprintf fmt "@[<hv 0>%a@]@ →@ @[<hv 0>%a@]"
          (pp_ty_prec PrecApp names) a
          (pp_ty_prec PrecPi (Some (fresh_name names) :: names))
          b
      in
      parens_if (needs_parens ctx_prec my_prec) fmt pp
  | TyPi (Some x, a, b) ->
      let my_prec = PrecPi in
      let pp fmt =
        Format.fprintf fmt "@[<hov 0>(%s :@;<1 2>%a) →@ %a@]" x
          (pp_ty_prec PrecFun names) a
          (pp_ty_prec PrecPi (Some x :: names))
          b
      in
      parens_if (needs_parens ctx_prec my_prec) fmt pp
  | TyEl (TmApp (TmApp (TmConst [ "Prod" ], a_code), b_code)) ->
      let my_prec = PrecPi in
      let pp fmt =
        Format.fprintf fmt "@[<hov 2>%a@ × %a@]" (pp_ty_prec PrecApp names)
          (TyEl a_code) (pp_ty_prec PrecPi names) (TyEl b_code)
      in
      parens_if (needs_parens ctx_prec my_prec) fmt pp
  | TyEl (TmApp (TmApp (TmConst [ "Sigma" ], _), TmLam (x_opt, x_ty, b_code)))
    ->
      let x = get_name_for_binding x_opt names in
      let my_prec = PrecPi in
      let pp fmt =
        Format.fprintf fmt "@[<hov 0>(%s :@;<1 2>%a) × %a@]" x
          (pp_ty_prec PrecFun names) x_ty
          (pp_ty_prec PrecPi (Some x :: names))
          (TyEl b_code)
      in
      parens_if (needs_parens ctx_prec my_prec) fmt pp
  | TyEl t -> pp_tm_prec ctx_prec names fmt t

and pp_tm_prec (ctx_prec : prec) (names : string option list) fmt : tm -> unit =
  let rec flatten_app acc = function
    | TmApp (f, a) -> flatten_app (a :: acc) f
    | head -> (head, acc)
  in
  function
  | TmVar (Idx l) ->
      let nm =
        if l < List.length names then
          Option.value (List.nth names l) ~default:"_"
        else
          Format.sprintf "idx%d†" l
      in
      Format.pp_print_string fmt nm
  | TmConst name -> Name.pp fmt name
  | TmLam (name, a, body) ->
      let my_prec = PrecFun in
      let x = get_name_for_binding name names in
      let pp fmt =
        Format.fprintf fmt "@[<hov 2>fun %s : %a =>@ %a@]" x
          (pp_ty_prec PrecFun names) a
          (pp_tm_prec PrecFun (Some x :: names))
          body
      in
      parens_if (needs_parens ctx_prec my_prec) fmt pp
  | TmPiHat (None, a, b) ->
      let my_prec = PrecPi in
      let pp fmt =
        Format.fprintf fmt "@[<hov>%a →@ %a@]" (pp_tm_prec PrecApp names) a
          (pp_tm_prec PrecPi (Some (fresh_name names) :: names))
          b
      in
      parens_if (needs_parens ctx_prec my_prec) fmt pp
  | TmPiHat (Some x, a, b) ->
      let my_prec = PrecPi in
      let pp fmt =
        Format.fprintf fmt "@[<hov 0>(%s :@;<1 2>%a) →@ %a@]" x
          (pp_tm_prec PrecFun names) a
          (pp_tm_prec PrecPi (Some x :: names))
          b
      in
      parens_if (needs_parens ctx_prec my_prec) fmt pp
  | TmSorry _ -> Format.fprintf fmt "sorry"
  | TmLet (x, ty, t, body) ->
      let my_prec = PrecLet in
      let pp fmt =
        Format.fprintf fmt "@[<v 0>@[<hov 2>let %s : %a :=@ %a;@]@ %a@]" x
          (pp_ty_prec PrecFun names) ty (pp_tm_prec PrecLet names) t
          (pp_tm_prec PrecLet (Some x :: names))
          body
      in
      parens_if (needs_parens ctx_prec my_prec) fmt pp
  | tm ->
      (* application or atom *)
      let head, args = flatten_app [] tm in
      let my_prec = PrecApp in
      let pp fmt =
        let pp_head fmt = pp_tm_prec my_prec names fmt head in
        let pp_args fmt = pp_list (pp_tm_prec PrecMax names) fmt args in
        Format.fprintf fmt "@[<hov 2>%t@ %t@]" pp_head pp_args
      in
      parens_if (needs_parens ctx_prec my_prec) fmt pp

let pp_ty_ctx = pp_ty_prec PrecLet
let pp_ty = pp_ty_prec PrecLet []
let pp_tm = pp_tm_prec PrecLet []

let pp_def fmt ((name, term, ty) : Name.t * tm * ty) : unit =
  Format.fprintf fmt "@[<v 0>@[<hov 2>def %a :@;<1 4>%a :=@]@;<0 2>%a@]" Name.pp
    name pp_ty ty pp_tm term

(* ========== Values ========== *)

let env_names (env : env) : string option list =
  List.init (List.length env) (fun _ -> None)

let rec pp_vty_ctx (names : string option list) fmt : vty -> unit = function
  | VTyU -> Format.fprintf fmt "Type"
  | VTyPi (None, a, clos) ->
      Format.fprintf fmt "@[<hov 2>%a →@ %a@]" (pp_vty_ctx names) a
        (pp_clos_ty None) clos
  | VTyPi (Some x, a, clos) ->
      Format.fprintf fmt "@[<hov 2>(%s : %a) →@ %a@]" x (pp_vty_ctx names) a
        (pp_clos_ty (Some x)) clos
  | VTyEl n -> pp_neutral_ctx names fmt n

and pp_vtm_ctx (names : string option list) fmt : vtm -> unit = function
  | VTmNeutral n -> pp_neutral_ctx names fmt n
  | VTmLam (x_opt, a, clos) ->
      Format.fprintf fmt "@[<hov 2>(fun %a : %a =>@ %a)@]" pp_name x_opt
        (pp_vty_ctx names) a (pp_clos_tm x_opt) clos
  | VTmPiHat (None, a, clos) ->
      Format.fprintf fmt "@[<hov 2>%a →@ %a@]" (pp_vtm_ctx names) a
        (pp_clos_tm None) clos
  | VTmPiHat (Some x, a, clos) ->
      Format.fprintf fmt "@[<hov 2>(%s : %a) →@ %a@]" x (pp_vtm_ctx names) a
        (pp_clos_tm (Some x)) clos

and pp_neutral_ctx (names : string option list) fmt ((head, sp) : neutral) :
    unit =
  match sp with
  | [] -> pp_head fmt head
  | _ ->
      Format.fprintf fmt "@[<hov 2>(%a@ %a)@]" pp_head head
        (pp_list (pp_vtm_ctx names))
        sp

and pp_head fmt : head -> unit = function
  | HVar (Lvl lvl) -> Format.fprintf fmt "lvl%d†" lvl
  | HConst name -> Name.pp fmt name
  | HSorry (id, _ty) -> Format.fprintf fmt "sorry_%d" id

and pp_clos_ty (x : string option) fmt : clos_ty -> unit = function
  | ClosTy (env, body) -> pp_ty_prec PrecLet (x :: env_names env) fmt body

and pp_clos_tm (x : string option) fmt : clos_tm -> unit = function
  | ClosTm (env, body) -> pp_tm_prec PrecLet (x :: env_names env) fmt body

let pp_vty fmt (ty : vty) : unit = pp_vty_ctx [] fmt ty
let pp_vtm fmt (tm : vtm) : unit = pp_vtm_ctx [] fmt tm
