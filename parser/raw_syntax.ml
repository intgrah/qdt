type t =
  | Ident of string
  | App of t * t
  | Lambda of string * t option * t
  | Pi of string * t * t
  | Arrow of t * t
  | Let of string * t option * t * t
  | Hole
  | Type

type def = string * t option * t
type program = def list

let rec pp (fmt : Format.formatter) (t : t) : unit =
  match t with
  | Ident name -> Format.fprintf fmt "%s" name
  | App (f, a) -> Format.fprintf fmt "@[<hov 2>(%a@ %a)@]" pp f pp a
  | Lambda (name, ty_opt, body) -> (
      match ty_opt with
      | None -> Format.fprintf fmt "@[<hov 2>(λ%s.@ %a)@]" name pp body
      | Some ty ->
          Format.fprintf fmt "@[<hov 2>(λ%s :@ %a.@ %a)@]" name pp ty pp body)
  | Pi (name, a, b) ->
      Format.fprintf fmt "@[<hov 2>(Π %s :@ %a.@ %a)@]" name pp a pp b
  | Arrow (a, b) -> Format.fprintf fmt "@[<hov 2>(%a@ →@ %a)@]" pp a pp b
  | Let (name, ty_opt, rhs, body) -> (
      match ty_opt with
      | None ->
          Format.fprintf fmt "@[<hov 2>(let %s :=@ %a@ in@ %a)@]" name pp rhs pp
            body
      | Some ty ->
          Format.fprintf fmt "@[<hov 2>(let %s :@ %a :=@ %a@ in@ %a)@]" name pp
            ty pp rhs pp body)
  | Hole -> Format.fprintf fmt "_"
  | Type -> Format.fprintf fmt "Type"

let pp_def (fmt : Format.formatter) ((name, ty_opt, body) : def) : unit =
  match ty_opt with
  | None -> Format.fprintf fmt "@[<hov 2>def %s :=@ %a@]" name pp body
  | Some ty ->
      Format.fprintf fmt "@[<hov 2>def %s :@ %a :=@ %a@]" name pp ty pp body

let pp_program (fmt : Format.formatter) (prog : program) : unit =
  Format.pp_print_list
    ~pp_sep:(fun fmt () -> Format.fprintf fmt "\n\n")
    pp_def fmt prog
