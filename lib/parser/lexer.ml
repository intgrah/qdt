type input = string
type pos = int

let is_whitespace c =
  c = ' ' || c = '\t' || c = '\n' || c = '\r'

let is_alpha c =
  (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')

let is_digit c =
  c >= '0' && c <= '9'

let is_alnum c =
  is_alpha c || is_digit c || c = '_' || c = '\''

let rec skip_whitespace (input : input) (pos : pos) : pos =
  if pos >= String.length input then
    pos
  else if is_whitespace input.[pos] then
    skip_whitespace input (pos + 1)
  else
    pos

let lex_ident (input : input) (pos : pos) : (string * pos) option =
  if pos >= String.length input || not (is_alpha input.[pos]) then
    None
  else
    let rec go i =
      if i >= String.length input || not (is_alnum input.[i]) then
        i
      else
        go (i + 1)
    in
    let end_pos = go pos in
    let name = String.sub input pos (end_pos - pos) in
    Some (name, end_pos)

let lex_token (input : input) (pos : pos) : (Token.t * pos) option =
  let pos = skip_whitespace input pos in
  if pos >= String.length input then
    None
  else
    match input.[pos] with
    | '(' -> Some (Token.LParen, pos + 1)
    | ')' -> Some (Token.RParen, pos + 1)
    | ':' ->
        if pos + 1 < String.length input && input.[pos + 1] = '=' then
          Some (Token.Colon_equals, pos + 2)
        else
          Some (Token.Colon, pos + 1)
    | '-' ->
        if pos + 1 < String.length input && input.[pos + 1] = '>' then
          Some (Token.Arrow, pos + 2)
        else
          None
    | c when is_alpha c ->
        (match lex_ident input pos with
         | None -> None
         | Some (name, pos') ->
             let tok = match name with
               | "let" -> Token.Let
               | "fun" -> Token.Fun
               | _ -> Token.Ident name
             in
             Some (tok, pos'))
    | _ -> None

let lex (input : input) : Token.t list option =
  let rec go pos acc =
    match lex_token input pos with
    | None ->
        let pos = skip_whitespace input pos in
        if pos >= String.length input then
          Some (List.rev acc)
        else
          None
    | Some (tok, pos') ->
        go pos' (tok :: acc)
  in
  go 0 []
