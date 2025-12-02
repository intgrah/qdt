open Syntax

(* ========== Raw Syntax ========== *)

let pp_name (fmt : Format.formatter) : string option -> unit = function
  | None -> Format.fprintf fmt "_"
  | Some name -> Format.fprintf fmt "%s" name

let rec pp_raw (fmt : Format.formatter) : raw -> unit = function
  | RIdent name -> Format.fprintf fmt "%s" name
  | RApp (f, a) -> Format.fprintf fmt "@[<hov 2>(%a@ %a)@]" pp_raw f pp_raw a
  | RLam (name, None, body) ->
      Format.fprintf fmt "@[<hov 2>(fun %a =>@ %a)@]" pp_name name pp_raw body
  | RLam (name, Some ty, body) ->
      Format.fprintf fmt "@[<hov 2>(fun %a : %a =>@ %a)@]" pp_name name pp_raw
        ty pp_raw body
  | RPi (name, a, b) ->
      Format.fprintf fmt "@[<hov 2>(%a : %a)@ -> %a@]" pp_name name pp_raw a
        pp_raw b
  | RArrow (a, b) -> Format.fprintf fmt "@[<hov 2>%a@ -> %a@]" pp_raw a pp_raw b
  | RLet (name, None, rhs, body) ->
      Format.fprintf fmt "@[<hov 2>(let %s :=@ %a@ in@ %a)@]" name pp_raw rhs
        pp_raw body
  | RLet (name, Some ty, rhs, body) ->
      Format.fprintf fmt "@[<hov 2>(let %s : %a :=@ %a@ in@ %a)@]" name pp_raw
        ty pp_raw rhs pp_raw body
  | RU -> Format.fprintf fmt "Type"
  | RUnit -> Format.fprintf fmt "Unit"
  | RUnitTm -> Format.fprintf fmt "()"
  | RPair (a, b) -> Format.fprintf fmt "@[<hov 2>(%a,@ %a)@]" pp_raw a pp_raw b
  | REq (a, b) -> Format.fprintf fmt "@[<hov 2>%a@ = %a@]" pp_raw a pp_raw b
  | RRefl t -> Format.fprintf fmt "@[<hov 2>(refl %a)@]" pp_raw t
  | RSigma (name, a, b) ->
      Format.fprintf fmt "@[<hov 2>(%a : %a)@ * %a@]" pp_name name pp_raw a
        pp_raw b
  | RProd (a, b) -> Format.fprintf fmt "@[<hov 2>%a@ * %a@]" pp_raw a pp_raw b
  | RProj1 t -> Format.fprintf fmt "@[<hov 2>(fst %a)@]" pp_raw t
  | RProj2 t -> Format.fprintf fmt "@[<hov 2>(snd %a)@]" pp_raw t
  | RInt -> Format.fprintf fmt "Int"
  | RIntLit n -> Format.fprintf fmt "%d" n
  | RAdd (a, b) -> Format.fprintf fmt "@[<hov 2>%a@ + %a@]" pp_raw a pp_raw b
  | RAnn (e, ty) ->
      Format.fprintf fmt "@[<hov 2>(%a@ : %a)@]" pp_raw e pp_raw ty

let pp_raw_def (fmt : Format.formatter) ((name, body) : raw_def) : unit =
  Format.fprintf fmt "@[<hov 2>def %s :=@ %a@]" name pp_raw body

let pp_raw_program (fmt : Format.formatter) (prog : raw_program) : unit =
  Format.pp_print_list
    ~pp_sep:(fun fmt () -> Format.fprintf fmt "\n\n")
    pp_raw_def fmt prog

(* ========== Core Syntax ========== *)

let fresh_name (names : string list) : string =
  "x" ^ string_of_int (List.length names)

let get_name (name_opt : string option) (names : string list) : string =
  match name_opt with
  | Some name -> name
  | None -> fresh_name names

let rec pp_ty_ctx (names : string list) (fmt : Format.formatter) : ty -> unit =
  function
  | TyU -> Format.fprintf fmt "Type"
  | TyPi (name_opt, a, b) ->
      let x = get_name name_opt names in
      Format.fprintf fmt "@[<hov 2>(%s : %a)@ -> %a@]" x (pp_ty_ctx names) a
        (pp_ty_ctx (x :: names))
        b
  | TyArrow (a, b) ->
      Format.fprintf fmt "@[<hov 2>%a@ -> %a@]" (pp_ty_ctx names) a
        (pp_ty_ctx names) b
  | TySigma (name_opt, a, b) ->
      let x = get_name name_opt names in
      Format.fprintf fmt "@[<hov 2>(%s : %a)@ * %a@]" x (pp_ty_ctx names) a
        (pp_ty_ctx (x :: names))
        b
  | TyProd (a, b) ->
      Format.fprintf fmt "@[<hov 2>%a@ * %a@]" (pp_ty_ctx names) a
        (pp_ty_ctx names) b
  | TyUnit -> Format.fprintf fmt "Unit"
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
  | TmLam (name_opt, a, _b, body) ->
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
  | TmPiHat (name_opt, a, b) ->
      let x = get_name name_opt names in
      Format.fprintf fmt "@[<hov 2>(%s : %a)@ -> %a@]" x (pp_tm_ctx names) a
        (pp_tm_ctx (x :: names))
        b
  | TmArrowHat (a, b) ->
      Format.fprintf fmt "@[<hov 2>%a@ -> %a@]" (pp_tm_ctx names) a
        (pp_tm_ctx names) b
  | TmSigmaHat (name_opt, a, b) ->
      let x = get_name name_opt names in
      Format.fprintf fmt "@[<hov 2>(%s : %a)@ * %a@]" x (pp_tm_ctx names) a
        (pp_tm_ctx (x :: names))
        b
  | TmProdHat (a, b) ->
      Format.fprintf fmt "@[<hov 2>%a@ * %a@]" (pp_tm_ctx names) a
        (pp_tm_ctx names) b
  | TmMkSigma (_a, _b, t, u) ->
      Format.fprintf fmt "@[<hov 2>(%a,@ %a)@]" (pp_tm_ctx names) t
        (pp_tm_ctx names) u
  | TmProj1 t -> Format.fprintf fmt "@[<hov 2>(fst %a)@]" (pp_tm_ctx names) t
  | TmProj2 t -> Format.fprintf fmt "@[<hov 2>(snd %a)@]" (pp_tm_ctx names) t
  | TmUnit -> Format.fprintf fmt "()"
  | TmIntLit n -> Format.fprintf fmt "%d" n
  | TmUnitHat -> Format.fprintf fmt "Unit"
  | TmIntHat -> Format.fprintf fmt "Int"
  | TmEqHat (_a, t, u) ->
      Format.fprintf fmt "@[<hov 2>%a@ = %a@]" (pp_tm_ctx names) t
        (pp_tm_ctx names) u
  | TmRefl (_a, e) ->
      Format.fprintf fmt "@[<hov 2>(refl %a)@]" (pp_tm_ctx names) e
  | TmAdd (a, b) ->
      Format.fprintf fmt "@[<hov 2>%a@ + %a@]" (pp_tm_ctx names) a
        (pp_tm_ctx names) b

let pp_ty fmt t = pp_ty_ctx [] fmt t
let pp_tm fmt t = pp_tm_ctx [] fmt t
let ty_to_string t = Format.asprintf "%a" pp_ty t
let tm_to_string t = Format.asprintf "%a" pp_tm t

let pp_def (fmt : Format.formatter) ((name, term, ty) : string * tm * ty) : unit
    =
  Format.fprintf fmt "@[<hov 2>def %s : %a :=@ %a@]" name pp_ty ty pp_tm term
