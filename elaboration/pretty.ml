open Syntax

(* ========== Raw Syntax ========== *)

let pp_name fmt : string option -> unit = function
  | None -> Format.fprintf fmt "_"
  | Some name -> Format.fprintf fmt "%s" name

let rec pp_binder fmt : Raw.binder -> unit = function
  | name, None -> pp_name fmt name
  | name, Some ty -> Format.fprintf fmt "(%a : %a)" pp_name name pp_raw ty

and pp_binder_group fmt ((names, ty) : Raw.binder_group) : unit =
  Format.fprintf fmt "(%a : %a)"
    (Format.pp_print_list ~pp_sep:Format.pp_print_space pp_name)
    names pp_raw ty

and pp_raw (fmt : Format.formatter) : Raw.t -> unit = function
  | Ident name -> Format.fprintf fmt "%s" name
  | App (f, a) -> Format.fprintf fmt "@[<hov 2>(%a@ %a)@]" pp_raw f pp_raw a
  | Lam (binders, body) ->
      Format.fprintf fmt "@[<hov 2>(fun %a =>@ %a)@]"
        (Format.pp_print_list ~pp_sep:Format.pp_print_space pp_binder)
        binders pp_raw body
  | Pi (group, b) ->
      Format.fprintf fmt "@[<hov 2>%a@ → %a@]" pp_binder_group group pp_raw b
  | Arrow (a, b) -> Format.fprintf fmt "@[<hov 2>%a@ → %a@]" pp_raw a pp_raw b
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
      Format.fprintf fmt "@[<hov 2>%a@ × %a@]" pp_binder_group group pp_raw b
  | Prod (a, b) -> Format.fprintf fmt "@[<hov 2>%a@ × %a@]" pp_raw a pp_raw b
  | Proj1 t -> Format.fprintf fmt "@[<hov 2>(fst %a)@]" pp_raw t
  | Proj2 t -> Format.fprintf fmt "@[<hov 2>(snd %a)@]" pp_raw t
  | Int -> Format.fprintf fmt "Int"
  | IntLit n -> Format.fprintf fmt "%d" n
  | Add (a, b) -> Format.fprintf fmt "@[<hov 2>%a@ + %a@]" pp_raw a pp_raw b
  | Sub (a, b) -> Format.fprintf fmt "@[<hov 2>%a@ - %a@]" pp_raw a pp_raw b
  | Ann (e, ty) -> Format.fprintf fmt "@[<hov 2>(%a@ : %a)@]" pp_raw e pp_raw ty
  | Sorry -> Format.fprintf fmt "sorry"

let pp_ctor fmt
    ((ctor_name, ctor_params, ctor_ty) :
      string * Raw.binder list * Raw.t option) : unit =
  match (ctor_params, ctor_ty) with
  | [], None -> Format.fprintf fmt "| %s" ctor_name
  | [], Some ty -> Format.fprintf fmt "| %s : %a" ctor_name pp_raw ty
  | params, None ->
      Format.fprintf fmt "| %s %a" ctor_name
        (Format.pp_print_list ~pp_sep:Format.pp_print_space pp_binder)
        params
  | params, Some ty ->
      Format.fprintf fmt "| %s %a : %a" ctor_name
        (Format.pp_print_list ~pp_sep:Format.pp_print_space pp_binder)
        params pp_raw ty

let pp_binder_group fmt ((names, ty) : Raw.binder_group) : unit =
  let pp_name fmt = function
    | Some n -> Format.fprintf fmt "%s" n
    | None -> Format.fprintf fmt "_"
  in
  Format.fprintf fmt "(%a : %a)"
    (Format.pp_print_list ~pp_sep:Format.pp_print_space pp_name)
    names pp_raw ty

let pp_raw_item (fmt : Format.formatter) : Raw.item -> unit = function
  | Def { name; body } ->
      Format.fprintf fmt "@[<hov 2>def %s :=@ %a@]" name pp_raw body
  | Example { body } ->
      Format.fprintf fmt "@[<hov 2>example :=@ %a@]" pp_raw body
  | Inductive { name; params; ty; ctors } -> (
      let pp_params fmt params =
        if params <> [] then
          Format.fprintf fmt " %a"
            (Format.pp_print_list ~pp_sep:Format.pp_print_space pp_binder_group)
            params
      in
      match ty with
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
  | Structure { name; params; ty; fields } -> (
      let pp_params fmt params =
        if params <> [] then
          Format.fprintf fmt " %a"
            (Format.pp_print_list ~pp_sep:Format.pp_print_space pp_binder_group)
            params
      in
      let pp_field fmt (fname, args, fty) =
        match args with
        | [] -> Format.fprintf fmt "(%s : %a)" fname pp_raw fty
        | args ->
            Format.fprintf fmt "(%s %a : %a)" fname
              (Format.pp_print_list ~pp_sep:Format.pp_print_space
                 pp_binder_group)
              args pp_raw fty
      in
      match ty with
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

let pp_raw_program (fmt : Format.formatter) (prog : Raw.program) : unit =
  Format.pp_print_list
    ~pp_sep:(fun fmt () -> Format.fprintf fmt "\n\n")
    pp_raw_item fmt prog

(* ========== Core Syntax ========== *)

let fresh_name (names : string list) : string =
  Format.sprintf "x%d†" (List.length names)

let get_name (name_opt : string option) (names : string list) : string =
  match name_opt with
  | Some name -> name
  | None -> fresh_name names

let rec pp_ty_ctx (names : string list) fmt : ty -> unit = function
  | TyU -> Format.fprintf fmt "Type"
  | TyPi (None, a, b) ->
      Format.fprintf fmt "@[<hov 2>%a@ → %a@]" (pp_ty_ctx names) a
        (pp_ty_ctx (fresh_name names :: names))
        b
  | TyPi (Some x, a, b) ->
      Format.fprintf fmt "@[<hov 2>(%s : %a)@ → %a@]" x (pp_ty_ctx names) a
        (pp_ty_ctx (x :: names))
        b
  | TySigma (None, a, b) ->
      Format.fprintf fmt "@[<hov 2>%a@ × %a@]" (pp_ty_ctx names) a
        (pp_ty_ctx (fresh_name names :: names))
        b
  | TySigma (Some x, a, b) ->
      Format.fprintf fmt "@[<hov 2>(%s : %a)@ × %a@]" x (pp_ty_ctx names) a
        (pp_ty_ctx (x :: names))
        b
  | TyInt -> Format.fprintf fmt "Int"
  | TyEl t -> Format.fprintf fmt "@[<hov 2>%a@]" (pp_tm_ctx names) t

and pp_tm_ctx (names : string list) (fmt : Format.formatter) : tm -> unit =
  function
  | TmVar (Idx l) ->
      if l < List.length names then
        Format.fprintf fmt "%s" (List.nth names l)
      else
        Format.fprintf fmt "x%d†" l
  | TmConst name -> Format.fprintf fmt "%a" Name.pp name
  | TmLam (name_opt, a, body) ->
      let x = get_name name_opt names in
      Format.fprintf fmt "@[<hov 2>(fun %s : %a =>@ %a)@]" x (pp_ty_ctx names) a
        (pp_tm_ctx (x :: names))
        body
  | TmApp ((TmLam _ as f), a) ->
      Format.fprintf fmt "@[<hov 2>(%a)@ (%a)@]" (pp_tm_ctx names) f
        (pp_tm_ctx names) a
  | TmApp (f, ((TmVar _ | TmConst _ | TmIntHat) as a)) ->
      Format.fprintf fmt "@[<hov 2>%a@ %a@]" (pp_tm_ctx names) f
        (pp_tm_ctx names) a
  | TmApp (f, a) ->
      Format.fprintf fmt "@[<hov 2>%a@ (%a)@]" (pp_tm_ctx names) f
        (pp_tm_ctx names) a
  | TmPiHat (None, a, b) ->
      Format.fprintf fmt "@[<hov 2>%a@ → %a@]" (pp_tm_ctx names) a
        (pp_tm_ctx (fresh_name names :: names))
        b
  | TmPiHat (Some x, a, b) ->
      Format.fprintf fmt "@[<hov 2>(%s : %a)@ → %a@]" x (pp_tm_ctx names) a
        (pp_tm_ctx (x :: names))
        b
  | TmSigmaHat (None, a, b) ->
      Format.fprintf fmt "@[<hov 2>%a@ × %a@]" (pp_tm_ctx names) a
        (pp_tm_ctx (fresh_name names :: names))
        b
  | TmSigmaHat (Some x, a, b) ->
      Format.fprintf fmt "@[<hov 2>(%s : %a)@ × %a@]" x (pp_tm_ctx names) a
        (pp_tm_ctx (x :: names))
        b
  | TmMkSigma (_a, _b, t, u) ->
      Format.fprintf fmt "@[<hov 2>(%a,@ %a)@]" (pp_tm_ctx names) t
        (pp_tm_ctx names) u
  | TmProj1 t -> Format.fprintf fmt "@[<hov 2>fst (%a)@]" (pp_tm_ctx names) t
  | TmProj2 t -> Format.fprintf fmt "@[<hov 2>snd (%a)@]" (pp_tm_ctx names) t
  | TmIntLit n -> Format.fprintf fmt "%d" n
  | TmIntHat -> Format.fprintf fmt "Int"
  | TmAdd (a, b) ->
      Format.fprintf fmt "@[<hov 2>%a@ + %a@]" (pp_tm_ctx names) a
        (pp_tm_ctx names) b
  | TmSub (a, b) ->
      Format.fprintf fmt "@[<hov 2>%a@ - %a@]" (pp_tm_ctx names) a
        (pp_tm_ctx names) b
  | TmSorry _ -> Format.fprintf fmt "sorry"
  | TmLet (x, ty, t, body) ->
      Format.fprintf fmt "@[<v 0>@[<hov 2>let %s : %a :=@ %a;@]@ %a@]" x
        (pp_ty_ctx names) ty (pp_tm_ctx names) t
        (pp_tm_ctx (x :: names))
        body

let pp_ty fmt t = pp_ty_ctx [] fmt t
let pp_tm fmt t = pp_tm_ctx [] fmt t
let ty_to_string t = Format.asprintf "%a" pp_ty t
let tm_to_string t = Format.asprintf "%a" pp_tm t

let pp_def (fmt : Format.formatter) ((name, term, ty) : Name.t * tm * ty) : unit
    =
  Format.fprintf fmt "@[<hv 2>@[<hov 4>def %a :@ %a :=@]@ %a@]" Name.pp name
    pp_ty ty pp_tm term
