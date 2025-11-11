exception Parse_error
exception Tokens_remaining

module Parser = struct
  type input = Token.t list
  type 'a t = input -> ('a * input) option

  let return (x : 'a) : 'a t = fun input -> Some (x, input)

  let ( let* ) (p : 'a t) (f : 'a -> 'b t) : 'b t =
   fun input ->
    match p input with
    | None -> None
    | Some (x, input') -> f x input'

  let ( <|> ) (p1 : 'a t) (p2 : 'a t) : 'a t =
   fun input ->
    match p1 input with
    | Some _ as result -> result
    | None -> p2 input

  let token (t : Token.t) : unit t = function
    | [] -> None
    | tok :: rest when tok = t -> Some ((), rest)
    | _ -> None

  let many (p : 'a t) : 'a list t =
    let rec go acc input =
      match p input with
      | None -> Some (List.rev acc, input)
      | Some (x, input') -> go (x :: acc) input'
    in
    go []
end

open Parser

let parse_ident : string t = function
  | Token.Ident name :: rest -> Some (name, rest)
  | _ -> None

let parse_parens (p : 'a t) : 'a t =
  let* () = token Token.LParen in
  let* x = p in
  let* () = token Token.RParen in
  return x

let rec parse_atom : Raw_syntax.t t =
 fun input ->
  (parse_fst <|> parse_snd <|> parse_var <|> parse_hole <|> parse_type
 <|> parse_unit <|> parse_pair <|> parse_unit_term
 <|> parse_parens parse_preterm)
    input

and parse_var : Raw_syntax.t t =
 fun input ->
  (let* name = parse_ident in
   return (Raw_syntax.RIdent name))
    input

and parse_hole : Raw_syntax.t t = function
  | Token.Underscore :: rest -> Some (Raw_syntax.RHole, rest)
  | _ -> None

and parse_type : Raw_syntax.t t = function
  | Token.Type :: rest -> Some (Raw_syntax.RU, rest)
  | _ -> None

and parse_unit : Raw_syntax.t t = function
  | Token.Unit :: rest -> Some (Raw_syntax.RUnit, rest)
  | _ -> None

and parse_unit_term : Raw_syntax.t t = function
  | Token.LParen :: Token.RParen :: rest -> Some (Raw_syntax.RUnitTerm, rest)
  | _ -> None

and parse_pair : Raw_syntax.t t =
 fun input ->
  (let* () = token Token.LParen in
   let* a = parse_preterm in
   let* () = token Token.Comma in
   let* b = parse_preterm in
   let* () = token Token.RParen in
   return (Raw_syntax.RPair (a, b)))
    input

and parse_fst : Raw_syntax.t t =
 fun input ->
  (let* () = token Token.Fst in
   let* t = parse_atom in
   return (Raw_syntax.RFst t))
    input

and parse_snd : Raw_syntax.t t =
 fun input ->
  (let* () = token Token.Snd in
   let* t = parse_atom in
   return (Raw_syntax.RSnd t))
    input

and parse_lambda : Raw_syntax.t t =
 fun input ->
  (let* _ = token Token.Fun in
   let* name = parse_ident in
   let* ty_opt =
     (let* _ = token Token.Colon in
      let* ty = parse_preterm in
      return (Some ty))
     <|> return None
   in
   let* _ = token Token.Eq_gt in
   let* body = parse_preterm in
   return (Raw_syntax.RLambda (name, ty_opt, body)))
    input

and parse_pi : Raw_syntax.t t = function
  | Token.Pi :: rest ->
      (let* name = parse_ident in
       let* _ = token Token.Colon in
       let* a = parse_preterm in
       let* _ = token Token.Comma in
       let* b = parse_preterm in
       return (Raw_syntax.RPi (name, a, b)))
        rest
  | _ -> None

and parse_arrow : Raw_syntax.t t =
 fun input ->
  (let* a = parse_app in
   let* _ = token Token.Hyphen_gt in
   let* b = parse_preterm in
   return (Raw_syntax.RArrow (a, b)))
    input

and parse_prod : Raw_syntax.t t =
 fun input ->
  (let* a = parse_app in
   let* _ = token Token.Times in
   let* b = parse_preterm in
   return (Raw_syntax.RProd (a, b)))
    input

and parse_app : Raw_syntax.t t =
 fun input ->
  (let* head = parse_atom in
   let* args = many parse_atom in
   return (List.fold_left (fun f a -> Raw_syntax.RApp (f, a)) head args))
    input

and parse_preterm : Raw_syntax.t t =
 fun input ->
  (parse_lambda <|> parse_pi <|> parse_prod <|> parse_arrow <|> parse_app) input

and parse_def : Raw_syntax.def t = function
  | Token.Def :: rest ->
      (let* name = parse_ident in
       let* ty_opt =
         (let* _ = token Token.Colon in
          let* ty = parse_preterm in
          return (Some ty))
         <|> return None
       in
       let* _ = token Token.Colon_eq in
       let* body = parse_preterm in
       return (name, ty_opt, body))
        rest
  | _ -> None

let parse_program : Raw_syntax.program t = many parse_def

let parse (input : Token.t list) : Raw_syntax.program =
  match parse_program input with
  | None -> raise Parse_error
  | Some (x, []) -> x
  | Some (_, _ :: _) -> raise Tokens_remaining
