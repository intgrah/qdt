module Parser = struct
  type input = Token.t list
  type 'a t = input -> ('a * input) option

  let return (x : 'a) : 'a t = fun input -> Some (x, input)

  let bind (p : 'a t) (f : 'a -> 'b t) : 'b t =
   fun input ->
    match p input with
    | None -> None
    | Some (x, input') -> f x input'

  let ( >>= ) = bind
  let ( let* ) = bind
  let ( >> ) p q = p >>= fun _ -> q
  let fail : 'a t = fun _input -> None

  let alt (p1 : 'a t) (p2 : 'a t) : 'a t =
   fun input ->
    match p1 input with
    | Some _ as result -> result
    | None -> p2 input

  let ( <|> ) = alt

  let peek : Token.t option t =
   fun input ->
    match input with
    | [] -> Some (None, input)
    | tok :: _ -> Some (Some tok, input)

  let satisfy (pred : Token.t -> bool) : Token.t t =
   fun input ->
    match input with
    | [] -> None
    | tok :: rest when pred tok -> Some (tok, rest)
    | _ -> None

  let token (t : Token.t) : unit t =
    let* _ = satisfy (fun tok -> tok = t) in
    return ()

  let many (p : 'a t) : 'a list t =
    let rec go acc input =
      match p input with
      | None -> Some (List.rev acc, input)
      | Some (x, input') -> go (x :: acc) input'
    in
    fun input -> go [] input

  let some (p : 'a t) : 'a list t =
    let* x = p in
    let* xs = many p in
    return (x :: xs)
end

open Parser

let parse_ident : string t =
 fun input ->
  match input with
  | Token.Ident name :: rest -> Some (name, rest)
  | _ -> None

let parse_parens (p : 'a t) : 'a t =
  let* () = token Token.LParen in
  let* x = p in
  let* () = token Token.RParen in
  return x

let rec parse_tm_atom : Cst.tm t =
 fun input -> (parse_var <|> parse_hole <|> parse_parens parse_tm) input

and parse_var : Cst.tm t =
 fun input ->
  (let* name = parse_ident in
   return (Cst.Var name))
    input

and parse_hole : Cst.tm t = function
  | Token.Underscore :: rest -> Some (Cst.Hole, rest)
  | _ -> None

and parse_lambda : Cst.tm t =
 fun input ->
  (let* _ = token Token.Fun in
   let* name = parse_ident in
   let* ty_opt =
     (let* _ = token Token.Colon in
      let* ty = parse_ty in
      return (Some ty))
     <|> return None
   in
   let* _ = token Token.Arrow in
   let* body = parse_tm in
   return (Cst.Lambda (name, ty_opt, body)))
    input

and parse_ann : Cst.tm t =
 fun input ->
  (let* tm = parse_tm_app in
   let* ty_opt =
     (let* _ = token Token.Colon in
      let* ty = parse_ty in
      return (Some ty))
     <|> return None
   in
   match ty_opt with
   | Some ty -> return (Cst.Ann (tm, ty))
   | None -> return tm)
    input

and parse_tm_app : Cst.tm t =
 fun input ->
  (let* head = parse_tm_atom in
   let* args = many parse_tm_atom in
   return (List.fold_left (fun f a -> Cst.App (f, a)) head args))
    input

and parse_tm : Cst.tm t = fun input -> (parse_lambda <|> parse_ann) input

and parse_ty_atom : Cst.ty t =
 fun input -> (parse_star <|> parse_ty_var <|> parse_parens parse_ty) input

and parse_star : Cst.ty t = function
  | Token.Ident "Type" :: rest -> Some (Cst.Star, rest)
  | _ -> None

and parse_ty_var : Cst.ty t =
 fun input ->
  (let* name = parse_ident in
   return (Cst.TVar name))
    input

and parse_pi : Cst.ty t = function
  | Token.Ident "forall" :: rest ->
      (let* name = parse_ident in
       let* _ = token Token.Colon in
       let* a = parse_ty in
       let* _ = token (Token.Ident ".") in
       let* b = parse_ty in
       return (Cst.Pi (name, a, b)))
        rest
  | _ -> None

and parse_arrow_ty : Cst.ty t =
 fun input ->
  (let* a = parse_ty_atom in
   let* _ = token Token.Arrow in
   let* b = parse_ty in
   return (Cst.Arrow (a, b)))
    input

and parse_ty : Cst.ty t =
 fun input -> (parse_pi <|> parse_arrow_ty <|> parse_ty_atom) input

let parse (p : 'a t) (input : Token.t list) : ('a, _) result =
  match p input with
  | None -> Error `Parse_error
  | Some (x, []) -> Ok x
  | Some (_, _ :: _) -> Error `Tokens_remaining
