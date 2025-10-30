type input = Token.t list
type pos = int

type 'a parser = input -> pos -> ('a * pos) option

let return (x : 'a) : 'a parser =
  fun _input pos -> Some (x, pos)

let bind (p : 'a parser) (f : 'a -> 'b parser) : 'b parser =
  fun input pos ->
    match p input pos with
    | None -> None
    | Some (x, pos') -> f x input pos'

let (>>=) = bind
let (let*) = bind

let (>>) p q = p >>= fun _ -> q

let fail : 'a parser =
  fun _input _pos -> None

let alt (p1 : 'a parser) (p2 : 'a parser) : 'a parser =
  fun input pos ->
    match p1 input pos with
    | Some _ as result -> result
    | None -> p2 input pos

let (<|>) = alt

let peek : Token.t option parser =
  fun input pos ->
    if pos >= List.length input then
      Some (None, pos)
    else
      Some (Some (List.nth input pos), pos)

let satisfy (pred : Token.t -> bool) : Token.t parser =
  fun input pos ->
    if pos >= List.length input then
      None
    else if pred (List.nth input pos) then
      Some (List.nth input pos, pos + 1)
    else
      None

let token (t : Token.t) : unit parser =
  let* _ = satisfy (fun tok -> tok = t) in
  return ()

let many (p : 'a parser) : 'a list parser =
  let rec go acc input pos =
    match p input pos with
    | None -> Some (List.rev acc, pos)
    | Some (x, pos') -> go (x :: acc) input pos'
  in
  fun input pos -> go [] input pos

let some (p : 'a parser) : 'a list parser =
  let* x = p in
  let* xs = many p in
  return (x :: xs)

let parse_ident : string parser =
  fun input pos ->
    if pos >= List.length input then
      None
    else
      match List.nth input pos with
      | Token.Ident name -> Some (name, pos + 1)
      | _ -> None

let parse_lparen : unit parser = token Token.LParen
let parse_rparen : unit parser = token Token.RParen
let parse_colon : unit parser = token Token.Colon
let parse_arrow : unit parser = token Token.Arrow
let parse_colon_equals : unit parser = token Token.Colon_equals
let parse_let : unit parser = token Token.Let
let parse_fun : unit parser = token Token.Fun

let parse_parens (p : 'a parser) : 'a parser =
  let* _ = parse_lparen in
  let* x = p in
  let* _ = parse_rparen in
  return x

let rec parse_tm_atom : Cst.tm parser =
  fun input pos ->
    (parse_var
     <|> parse_hole
     <|> parse_parens parse_tm) input pos

and parse_var : Cst.tm parser =
  fun input pos ->
    (parse_ident >>= fun name ->
     return (Cst.Var name)) input pos

and parse_hole : Cst.tm parser =
  fun input pos ->
    if pos >= List.length input then
      None
    else
      match List.nth input pos with
      | Token.Ident "_" -> Some (Cst.Hole, pos + 1)
      | _ -> None

and parse_lambda : Cst.tm parser =
  fun input pos ->
    (parse_fun >>= fun _ ->
     parse_ident >>= fun name ->
     ((parse_colon >>= fun _ ->
       parse_ty >>= fun ty ->
       return (Some ty))
      <|> return None) >>= fun ty_opt ->
     parse_arrow >>= fun _ ->
     parse_tm >>= fun body ->
     return (Cst.Lambda (name, ty_opt, body))) input pos

and parse_ann : Cst.tm parser =
  fun input pos ->
    (parse_tm_app >>= fun tm ->
     ((parse_colon >>= fun _ ->
       parse_ty >>= fun ty ->
       return (Some ty))
      <|> return None) >>= fun ty_opt ->
     match ty_opt with
     | Some ty -> return (Cst.Ann (tm, ty))
     | None -> return tm) input pos

and parse_tm_app : Cst.tm parser =
  fun input pos ->
    (parse_tm_atom >>= fun head ->
     many parse_tm_atom >>= fun args ->
     return (List.fold_left (fun f a -> Cst.App (f, a)) head args)) input pos

and parse_tm : Cst.tm parser =
  fun input pos ->
    (parse_lambda <|> parse_ann) input pos

and parse_ty_atom : Cst.ty parser =
  fun input pos ->
    (parse_star
     <|> parse_ty_var
     <|> parse_parens parse_ty) input pos

and parse_star : Cst.ty parser =
  fun input pos ->
    if pos >= List.length input then
      None
    else
      match List.nth input pos with
      | Token.Ident "Type" -> Some (Cst.Star, pos + 1)
      | _ -> None

and parse_ty_var : Cst.ty parser =
  fun input pos ->
    (parse_ident >>= fun name ->
     return (Cst.TVar name)) input pos

and parse_pi : Cst.ty parser =
  fun input pos ->
    if pos >= List.length input then
      None
    else
      match List.nth input pos with
      | Token.Ident "forall" ->
          (return () >>= fun _ ->
           parse_ident >>= fun name ->
           parse_colon >>= fun _ ->
           parse_ty >>= fun a ->
           token (Token.Ident ".") >>= fun _ ->
           parse_ty >>= fun b ->
           return (Cst.Pi (name, a, b))) input (pos + 1)
      | _ -> None

and parse_arrow_ty : Cst.ty parser =
  fun input pos ->
    (parse_ty_atom >>= fun a ->
     parse_arrow >>= fun _ ->
     parse_ty >>= fun b ->
     return (Cst.Arrow (a, b))) input pos

and parse_ty : Cst.ty parser =
  fun input pos ->
    (parse_pi <|> parse_arrow_ty <|> parse_ty_atom) input pos

let parse (p : 'a parser) (input : Token.t list) : ('a, string) result =
  match p input 0 with
  | None -> Error "parse error"
  | Some (x, pos) ->
      if pos = List.length input then
        Ok x
      else
        Error ("unexpected token at position " ^ string_of_int pos)
