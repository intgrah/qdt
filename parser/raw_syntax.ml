type t =
  | RIdent of string
  | RApp of t * t
  | RLambda of string * t option * t
  | RPi of string * t * t
  | RArrow of t * t
  | RLet of string * t option * t * t
  | RHole
  | RU
  | RUnit
  | RUnitTerm
  | RProd of t * t
  | RPair of t * t
  | RFst of t
  | RSnd of t

type def = string * t option * t
type program = def list

let rec pp (fmt : Format.formatter) (t : t) : unit =
  match t with
  | RIdent name -> Format.fprintf fmt "%s" name
  | RApp (f, a) -> Format.fprintf fmt "@[<hov 2>(%a@ %a)@]" pp f pp a
  | RLambda (name, ty_opt, body) -> (
      match ty_opt with
      | None -> Format.fprintf fmt "@[<hov 2>(λ%s.@ %a)@]" name pp body
      | Some ty ->
          Format.fprintf fmt "@[<hov 2>(λ%s :@ %a.@ %a)@]" name pp ty pp body)
  | RPi (name, a, b) ->
      Format.fprintf fmt "@[<hov 2>(Π %s :@ %a.@ %a)@]" name pp a pp b
  | RArrow (a, b) -> Format.fprintf fmt "@[<hov 2>(%a@ →@ %a)@]" pp a pp b
  | RLet (name, ty_opt, rhs, body) -> (
      match ty_opt with
      | None ->
          Format.fprintf fmt "@[<hov 2>(let %s :=@ %a@ in@ %a)@]" name pp rhs pp
            body
      | Some ty ->
          Format.fprintf fmt "@[<hov 2>(let %s :@ %a :=@ %a@ in@ %a)@]" name pp
            ty pp rhs pp body)
  | RHole -> Format.fprintf fmt "_"
  | RU -> Format.fprintf fmt "Type"
  | RUnit -> Format.fprintf fmt "Unit"
  | RUnitTerm -> Format.fprintf fmt "()"
  | RProd (a, b) -> Format.fprintf fmt "@[<hov 2>%a@ ×@ %a@]" pp a pp b
  | RPair (a, b) -> Format.fprintf fmt "@[<hov 2>(%a,@ %a)@]" pp a pp b
  | RFst t -> Format.fprintf fmt "@[<hov 2>fst@ %a@]" pp t
  | RSnd t -> Format.fprintf fmt "@[<hov 2>snd@ %a@]" pp t

let pp_def (fmt : Format.formatter) ((name, ty_opt, body) : def) : unit =
  match ty_opt with
  | None -> Format.fprintf fmt "@[<hov 2>def %s :=@ %a@]" name pp body
  | Some ty ->
      Format.fprintf fmt "@[<hov 2>def %s :@ %a :=@ %a@]" name pp ty pp body

let pp_program (fmt : Format.formatter) (prog : program) : unit =
  Format.pp_print_list
    ~pp_sep:(fun fmt () -> Format.fprintf fmt "\n\n")
    pp_def fmt prog
