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
  | Fst
  | Snd
  | Sorry
  | Example
  | Inductive
  | Where
  | Type
  | Int
  | Underscore
  | Ident of string
  | IntLit of int

let pp_token (fmt : Format.formatter) : token -> unit = function
  | LParen -> Format.fprintf fmt "("
  | RParen -> Format.fprintf fmt ")"
  | Colon -> Format.fprintf fmt ":"
  | Arrow -> Format.fprintf fmt "→"
  | Eq_gt -> Format.fprintf fmt "=>"
  | Comma -> Format.fprintf fmt ","
  | Colon_eq -> Format.fprintf fmt ":="
  | Semicolon -> Format.fprintf fmt ";"
  | Times -> Format.fprintf fmt "×"
  | Plus -> Format.fprintf fmt "+"
  | Minus -> Format.fprintf fmt "-"
  | Equal -> Format.fprintf fmt "="
  | Pipe -> Format.fprintf fmt "|"
  | Def -> Format.fprintf fmt "def"
  | Let -> Format.fprintf fmt "let"
  | Fun -> Format.fprintf fmt "fun"
  | Fst -> Format.fprintf fmt "fst"
  | Snd -> Format.fprintf fmt "snd"
  | Sorry -> Format.fprintf fmt "sorry"
  | Example -> Format.fprintf fmt "example"
  | Inductive -> Format.fprintf fmt "inductive"
  | Where -> Format.fprintf fmt "where"
  | Type -> Format.fprintf fmt "Type"
  | Int -> Format.fprintf fmt "Int"
  | Underscore -> Format.fprintf fmt "_"
  | Ident s -> Format.fprintf fmt "%s" s
  | IntLit n -> Format.fprintf fmt "%d" n

exception Unterminated_comment
exception Illegal_character

let is_alpha_num = function
  | '0' .. '9'
  | 'A' .. 'Z'
  | 'a' .. 'z'
  | '_'
  | '.' ->
      true
  | _ -> false

let is_digit = function
  | '0' .. '9' -> true
  | _ -> false

let rec scan_int front = function
  | c :: cs when is_digit c -> scan_int (c :: front) cs
  | rest ->
      (front |> List.rev |> List.to_seq |> String.of_seq |> int_of_string, rest)

let rec scan_ident front = function
  | c :: cs when is_alpha_num c -> scan_ident (c :: front) cs
  | rest -> (front |> List.rev |> List.to_seq |> String.of_seq, rest)

let rec skip_block_comment depth = function
  | [] -> raise Unterminated_comment
  | '/' :: '-' :: cs -> skip_block_comment (depth + 1) cs
  | '-' :: '/' :: cs ->
      if depth = 0 then
        cs
      else
        skip_block_comment (depth - 1) cs
  | _ :: cs -> skip_block_comment depth cs

let rec skip_line_comment = function
  | [] -> []
  | '\n' :: cs -> cs
  | _ :: cs -> skip_line_comment cs

let rec scan front_toks = function
  | [] -> List.rev front_toks
  | '/' :: '-' :: cs -> scan front_toks (skip_block_comment 0 cs)
  | '-' :: '-' :: cs -> scan front_toks (skip_line_comment cs)
  | '=' :: '>' :: cs -> scan (Eq_gt :: front_toks) cs
  | '=' :: cs -> scan (Equal :: front_toks) cs
  | '-' :: '>' :: cs -> scan (Arrow :: front_toks) cs
  | '-' :: cs -> scan (Minus :: front_toks) cs
  | ':' :: '=' :: cs -> scan (Colon_eq :: front_toks) cs
  | ':' :: cs -> scan (Colon :: front_toks) cs
  | ',' :: cs -> scan (Comma :: front_toks) cs
  | ';' :: cs -> scan (Semicolon :: front_toks) cs
  | '(' :: cs -> scan (LParen :: front_toks) cs
  | ')' :: cs -> scan (RParen :: front_toks) cs
  | '|' :: cs -> scan (Pipe :: front_toks) cs
  | '*' :: cs -> scan (Times :: front_toks) cs
  | '+' :: cs -> scan (Plus :: front_toks) cs
  (* → in UTF-8 *)
  | '\xE2' :: '\x86' :: '\x92' :: cs -> scan (Arrow :: front_toks) cs
  (* × in UTF-8 *)
  | '\xC3' :: '\x97' :: cs -> scan (Times :: front_toks) cs
  | (' ' | '\t' | '\n') :: cs -> scan front_toks cs
  | c :: cs when is_digit c ->
      let n, cs = scan_int [ c ] cs in
      scan (IntLit n :: front_toks) cs
  | c :: cs when is_alpha_num c ->
      let tok, cs = scan_ident [ c ] cs in
      let tok =
        match tok with
        | "_" -> Underscore
        | "def" -> Def
        | "let" -> Let
        | "fun" -> Fun
        | "Type" -> Type
        | "Int" -> Int
        | "fst" -> Fst
        | "snd" -> Snd
        | "sorry" -> Sorry
        | "example" -> Example
        | "inductive" -> Inductive
        | "where" -> Where
        | tok -> Ident tok
      in
      scan (tok :: front_toks) cs
  | _ -> raise Illegal_character
