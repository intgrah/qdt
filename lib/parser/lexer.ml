let is_alpha_num = function
  | '0' .. '9'
  | 'A' .. 'Z'
  | 'a' .. 'z' ->
      true
  | _ -> false

let rec scan_ident front = function
  | c :: cs when is_alpha_num c -> scan_ident (c :: front) cs
  | rest ->
      (Token.Ident (front |> List.rev |> List.to_seq |> String.of_seq), rest)

let rec scan front_toks = function
  | [] -> List.rev front_toks
  | '-' :: '>' :: cs -> scan (Token.Arrow :: front_toks) cs
  | ':' :: '=' :: cs -> scan (Token.Colon_equals :: front_toks) cs
  | ':' :: cs -> scan (Token.Colon :: front_toks) cs
  | '(' :: cs -> scan (Token.LParen :: front_toks) cs
  | ')' :: cs -> scan (Token.RParen :: front_toks) cs
  | '_' :: cs -> scan (Token.Underscore :: front_toks) cs
  | (' ' | '\t' | '\n') :: cs -> scan front_toks cs
  | c :: cs when is_alpha_num c ->
      let tok, cs = scan_ident [ c ] cs in
      let tok =
        match tok with
        | Token.Ident "let" -> Token.Let
        | Token.Ident "fun" -> Token.Fun
        | tok -> tok
      in
      scan (tok :: front_toks) cs
  | _ -> failwith "Illegal character"
