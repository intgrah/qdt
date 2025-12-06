open Syntax

(* ========== Raw Syntax ========== *)

let pp_name (fmt : Format.formatter) : string option -> unit = function
  | None -> Format.fprintf fmt "_"
  | Some name -> Format.fprintf fmt "%s" name

let rec pp_binder (fmt : Format.formatter) : binder -> unit = function
  | name, None -> pp_name fmt name
  | name, Some ty -> Format.fprintf fmt "(%a : %a)" pp_name name pp_raw ty

and pp_binder_group (fmt : Format.formatter) ((names, ty) : binder_group) : unit
    =
  Format.fprintf fmt "(%a : %a)"
    (Format.pp_print_list ~pp_sep:Format.pp_print_space pp_name)
    names pp_raw ty

and pp_raw (fmt : Format.formatter) : raw -> unit = function
  | RIdent name -> Format.fprintf fmt "%s" name
  | RApp (f, a) -> Format.fprintf fmt "@[<hov 2>(%a@ %a)@]" pp_raw f pp_raw a
  | RLam (binders, body) ->
      Format.fprintf fmt "@[<hov 2>(fun %a =>@ %a)@]"
        (Format.pp_print_list ~pp_sep:Format.pp_print_space pp_binder)
        binders pp_raw body
  | RPi (group, b) ->
      Format.fprintf fmt "@[<hov 2>%a@ → %a@]" pp_binder_group group pp_raw b
  | RArrow (a, b) -> Format.fprintf fmt "@[<hov 2>%a@ → %a@]" pp_raw a pp_raw b
  | RLet (name, None, rhs, body) ->
      Format.fprintf fmt "@[<hov 2>(let %s :=@ %a@ in@ %a)@]" name pp_raw rhs
        pp_raw body
  | RLet (name, Some ty, rhs, body) ->
      Format.fprintf fmt "@[<hov 2>(let %s : %a :=@ %a@ in@ %a)@]" name pp_raw
        ty pp_raw rhs pp_raw body
  | RU -> Format.fprintf fmt "Type"
  | RUnit -> Format.fprintf fmt "Unit"
  | REmpty -> Format.fprintf fmt "Empty"
  | RUnitTm -> Format.fprintf fmt "()"
  | RAbsurd e -> Format.fprintf fmt "@[<hov 2>(absurd %a)@]" pp_raw e
  | RPair (a, b) -> Format.fprintf fmt "@[<hov 2>(%a,@ %a)@]" pp_raw a pp_raw b
  | REq (a, b) -> Format.fprintf fmt "@[<hov 2>%a@ = %a@]" pp_raw a pp_raw b
  | RRefl t -> Format.fprintf fmt "@[<hov 2>(refl %a)@]" pp_raw t
  | RSigma (group, b) ->
      Format.fprintf fmt "@[<hov 2>%a@ × %a@]" pp_binder_group group pp_raw b
  | RProd (a, b) -> Format.fprintf fmt "@[<hov 2>%a@ × %a@]" pp_raw a pp_raw b
  | RProj1 t -> Format.fprintf fmt "@[<hov 2>(fst %a)@]" pp_raw t
  | RProj2 t -> Format.fprintf fmt "@[<hov 2>(snd %a)@]" pp_raw t
  | RInt -> Format.fprintf fmt "Int"
  | RIntLit n -> Format.fprintf fmt "%d" n
  | RAdd (a, b) -> Format.fprintf fmt "@[<hov 2>%a@ + %a@]" pp_raw a pp_raw b
  | RSub (a, b) -> Format.fprintf fmt "@[<hov 2>%a@ - %a@]" pp_raw a pp_raw b
  | RAnn (e, ty) ->
      Format.fprintf fmt "@[<hov 2>(%a@ : %a)@]" pp_raw e pp_raw ty
  | RSorry -> Format.fprintf fmt "sorry"

let pp_raw_item (fmt : Format.formatter) : raw_item -> unit = function
  | RDef (name, body) ->
      Format.fprintf fmt "@[<hov 2>def %s :=@ %a@]" name pp_raw body
  | RExample body -> Format.fprintf fmt "@[<hov 2>example :=@ %a@]" pp_raw body

let pp_raw_program (fmt : Format.formatter) (prog : raw_program) : unit =
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

let rec pp_ty_ctx (names : string list) (fmt : Format.formatter) : ty -> unit =
  function
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
  | TyUnit -> Format.fprintf fmt "Unit"
  | TyEmpty -> Format.fprintf fmt "Empty"
  | TyInt -> Format.fprintf fmt "Int"
  | TyEq (e1, e2, _a) ->
      Format.fprintf fmt "@[<hov 2>%a@ = %a@]" (pp_tm_ctx names) e1
        (pp_tm_ctx names) e2
  | TyEl t -> Format.fprintf fmt "@[<hov 2>%a@]" (pp_tm_ctx names) t

and pp_tm_ctx (names : string list) (fmt : Format.formatter) : tm -> unit =
  function
  | TmVar idx ->
      if idx >= 0 && idx < List.length names then
        Format.fprintf fmt "%s" (List.nth names idx)
      else
        Format.fprintf fmt "#%d" idx
  | TmConst name -> Format.fprintf fmt "%s" name
  | TmLam (name_opt, a, body) ->
      let x = get_name name_opt names in
      Format.fprintf fmt "@[<hov 2>(fun %s : %a =>@ %a)@]" x (pp_ty_ctx names) a
        (pp_tm_ctx (x :: names))
        body
  | TmApp ((TmLam _ as f), a) ->
      Format.fprintf fmt "@[<hov 2>(%a)@ (%a)@]" (pp_tm_ctx names) f
        (pp_tm_ctx names) a
  | TmApp (f, ((TmVar _ | TmUnit) as a)) ->
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
  | TmProj1 t -> Format.fprintf fmt "@[<hov 2>(fst %a)@]" (pp_tm_ctx names) t
  | TmProj2 t -> Format.fprintf fmt "@[<hov 2>(snd %a)@]" (pp_tm_ctx names) t
  | TmUnit -> Format.fprintf fmt "()"
  | TmAbsurd (_c, e) ->
      Format.fprintf fmt "@[<hov 2>(absurd %a)@]" (pp_tm_ctx names) e
  | TmIntLit n -> Format.fprintf fmt "%d" n
  | TmUnitHat -> Format.fprintf fmt "Unit"
  | TmEmptyHat -> Format.fprintf fmt "Empty"
  | TmIntHat -> Format.fprintf fmt "Int"
  | TmEqHat (t, u, _) ->
      Format.fprintf fmt "@[<hov 2>%a@ = %a@]" (pp_tm_ctx names) t
        (pp_tm_ctx names) u
  | TmRefl (_a, e) ->
      Format.fprintf fmt "@[<hov 2>(refl %a)@]" (pp_tm_ctx names) e
  | TmAdd (a, b) ->
      Format.fprintf fmt "@[<hov 2>%a@ + %a@]" (pp_tm_ctx names) a
        (pp_tm_ctx names) b
  | TmSub (a, b) ->
      Format.fprintf fmt "@[<hov 2>%a@ - %a@]" (pp_tm_ctx names) a
        (pp_tm_ctx names) b
  | TmSorry _ -> Format.fprintf fmt "sorry"
  | TmLet (x, ty, t, body) ->
      Format.fprintf fmt "@[<hov 2>let %s : %a :=@ %a;@ %a@]" x
        (pp_ty_ctx names) ty (pp_tm_ctx names) t
        (pp_tm_ctx (x :: names))
        body

let pp_ty fmt t = pp_ty_ctx [] fmt t
let pp_tm fmt t = pp_tm_ctx [] fmt t
let ty_to_string t = Format.asprintf "%a" pp_ty t
let tm_to_string t = Format.asprintf "%a" pp_tm t

let pp_def (fmt : Format.formatter) ((name, term, ty) : string * tm * ty) : unit
    =
  Format.fprintf fmt "@[<hv 2>@[<hov 4>def %s :@ %a :=@]@ %a@]" name pp_ty ty
    pp_tm term
