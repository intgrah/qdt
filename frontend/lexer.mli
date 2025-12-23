type token =
  | LParen
  | RParen
  | Colon
  | Arrow
  | Eq_gt
  | Comma
  | Colon_eq
  | Semicolon
  | Times
  | Plus
  | Minus
  | Equal
  | Pipe
  | Def
  | Let
  | Fun
  | Sorry
  | Example
  | Inductive
  | Structure
  | Where
  | Import
  | Type
  | Underscore
  | Ident of string
  | NatLit of int

val pp_token : Format.formatter -> token -> unit

exception Unterminated_comment
exception Illegal_character of char

val scan : token list -> char list -> token list
