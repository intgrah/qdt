type t =
  | LParen
  | RParen
  | Colon
  | Hyphen_gt
  | Eq_gt
  | Comma
  | Colon_eq
  | Def
  | Let
  | Fun
  | Pi
  | Type
  | Unit
  | Underscore
  | Ident of string

let pp (fmt : Format.formatter) : t -> unit = function
  | LParen -> Format.fprintf fmt "("
  | RParen -> Format.fprintf fmt ")"
  | Colon -> Format.fprintf fmt ":"
  | Hyphen_gt -> Format.fprintf fmt "->"
  | Eq_gt -> Format.fprintf fmt "=>"
  | Comma -> Format.fprintf fmt ","
  | Colon_eq -> Format.fprintf fmt ":="
  | Def -> Format.fprintf fmt "def"
  | Let -> Format.fprintf fmt "let"
  | Fun -> Format.fprintf fmt "fun"
  | Pi -> Format.fprintf fmt "Pi"
  | Type -> Format.fprintf fmt "Type"
  | Unit -> Format.fprintf fmt "Unit"
  | Underscore -> Format.fprintf fmt "_"
  | Ident s -> Format.fprintf fmt "%s" s
