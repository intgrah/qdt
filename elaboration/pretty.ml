open Syntax

let rec pp_tm (fmt : Format.formatter) (t : tm) : unit =
  match t with
  | Var ix -> Format.fprintf fmt "#%d" ix
  | Lam (x, body) -> Format.fprintf fmt "@[<hov 2>(λ%s.@ %a)@]" x pp_tm body
  | App (f, a) -> (
      match f with
      | Lam _ -> Format.fprintf fmt "@[<hov 2>(%a)@ (%a)@]" pp_tm f pp_tm a
      | _ -> (
          match a with
          | Var _
          | Meta _
          | U ->
              Format.fprintf fmt "@[<hov 2>%a@ %a@]" pp_tm f pp_tm a
          | _ -> Format.fprintf fmt "@[<hov 2>%a@ (%a)@]" pp_tm f pp_tm a))
  | U -> Format.fprintf fmt "U"
  | Pi (x, a, b) ->
      if x = "_" then
        Format.fprintf fmt "@[<hov 2>%a@ →@ %a@]" pp_tm a pp_tm b
      else
        Format.fprintf fmt "@[<hov 2>(Π %s :@ %a.@ %a)@]" x pp_tm a pp_tm b
  | Let (x, ty, t, u) ->
      Format.fprintf fmt "@[<hov 2>(let %s :@ %a :=@ %a@ in@ %a)@]" x pp_tm ty
        pp_tm t pp_tm u
  | Meta m -> Format.fprintf fmt "?%d" m
  | InsertedMeta (m, bds) ->
      let bound_count =
        List.fold_left
          (fun acc bd ->
            match bd with
            | Bound -> acc + 1
            | Defined -> acc)
          0 bds
      in
      Format.fprintf fmt "?%d[%d]" m bound_count
  | Unit -> Format.fprintf fmt "Unit"
  | UnitTerm -> Format.fprintf fmt "()"

let pp_val (fmt : Format.formatter) (v : val_ty) : unit =
  let tm = Quote.quote 0 v in
  pp_tm fmt tm

let tm_to_string (t : tm) : string = Format.asprintf "%a" pp_tm t
let val_to_string (v : val_ty) : string = Format.asprintf "%a" pp_val v
