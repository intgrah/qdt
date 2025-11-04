open Syntax

let rec pp_tm (fmt : Format.formatter) (t : tm) : unit =
  match t with
  | Var ix -> Format.fprintf fmt "#%d" ix
  | Lam (ty, body) ->
      Format.fprintf fmt "@[<hov 2>(λ@ :@ %a.@ %a)@]" pp_ty ty pp_tm body
  | App (f, a) -> (
      match f with
      | Lam _ -> Format.fprintf fmt "@[<hov 2>(%a)@ (%a)@]" pp_tm f pp_tm a
      | _ -> (
          match a with
          | Var _
          | Meta _ ->
              Format.fprintf fmt "@[<hov 2>%a@ %a@]" pp_tm f pp_tm a
          | _ -> Format.fprintf fmt "@[<hov 2>%a@ (%a)@]" pp_tm f pp_tm a))
  | Meta m -> Format.fprintf fmt "?%d" m

and pp_ty (fmt : Format.formatter) (ty : ty) : unit =
  match ty with
  | TVar ix -> Format.fprintf fmt "#%d" ix
  | Pi (a, b) -> Format.fprintf fmt "@[<hov 2>(Π@ %a@ .@ %a)@]" pp_ty a pp_ty b
  | Type -> Format.fprintf fmt "Type"

let pp_ty_val (fmt : Format.formatter) (ty : ty_val) : unit =
  let ty_quoted = Quote.quote_ty 0 ty in
  pp_ty fmt ty_quoted

let tm_to_string (t : tm) : string = Format.asprintf "%a" pp_tm t
let ty_to_string (ty : ty) : string = Format.asprintf "%a" pp_ty ty
let ty_val_to_string (ty : ty_val) : string = Format.asprintf "%a" pp_ty_val ty
