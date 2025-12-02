type token =
  | LParen
  | RParen
  | Colon
  | Arrow
  | Eq_gt
  | Comma
  | Colon_eq
  | Times
  | Plus
  | Equal
  | Def
  | Let
  | Fun
  | Fst
  | Snd
  | Refl
  | Type
  | Unit
  | Int
  | Underscore
  | Ident of string
  | IntLit of int

val pp_token : Format.formatter -> token -> unit

exception Unterminated_comment
exception Illegal_character

val scan : token list -> char list -> token list
