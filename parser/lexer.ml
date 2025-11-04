exception Unterminated_comment
exception Illegal_character

let is_alpha_num = function
  | '0' .. '9'
  | 'A' .. 'Z'
  | 'a' .. 'z' ->
      true
  | _ -> false

let rec scan_ident front = function
  | c :: cs when is_alpha_num c -> scan_ident (c :: front) cs
  | rest -> (front |> List.rev |> List.to_seq |> String.of_seq, rest)

let rec skip_comment depth = function
  | [] -> raise Unterminated_comment
  | '(' :: '*' :: cs -> skip_comment (depth + 1) cs (* nested comment *)
  | '*' :: ')' :: cs -> if depth = 0 then cs else skip_comment (depth - 1) cs
  | _ :: cs -> skip_comment depth cs

let rec scan front_toks = function
  | [] -> List.rev front_toks
  | '(' :: '*' :: cs -> scan front_toks (skip_comment 0 cs)
  | '=' :: '>' :: cs -> scan (Token.Eq_gt :: front_toks) cs
  | '-' :: '>' :: cs -> scan (Token.Hyphen_gt :: front_toks) cs
  | ':' :: '=' :: cs -> scan (Token.Colon_eq :: front_toks) cs
  | ':' :: cs -> scan (Token.Colon :: front_toks) cs
  | ',' :: cs -> scan (Token.Comma :: front_toks) cs
  | '(' :: cs -> scan (Token.LParen :: front_toks) cs
  | ')' :: cs -> scan (Token.RParen :: front_toks) cs
  | '_' :: cs -> scan (Token.Underscore :: front_toks) cs
  (* λ in UTF-8 *)
  | '\xCE' :: '\xBB' :: cs -> scan (Token.Fun :: front_toks) cs
  (* Π in UTF-8 *)
  | '\xCE' :: '\xA0' :: cs -> scan (Token.Pi :: front_toks) cs
  (* ∀ in UTF-8 *)
  | '\xE2' :: '\x88' :: '\x80' :: cs -> scan (Token.Pi :: front_toks) cs
  | (' ' | '\t' | '\n') :: cs -> scan front_toks cs
  | c :: cs when is_alpha_num c ->
      let tok, cs = scan_ident [ c ] cs in
      let tok =
        match tok with
        | "def" -> Token.Def
        | "let" -> Token.Let
        | "fun" -> Token.Fun
        | "forall" -> Token.Pi
        | "Type" -> Token.Type
        | tok -> Token.Ident tok
      in
      scan (tok :: front_toks) cs
  | _ -> raise Illegal_character
