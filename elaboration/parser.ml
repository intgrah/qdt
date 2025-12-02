open Syntax

exception Parse_error of string
exception Tokens_remaining of Lexer.token list

module Parser = struct
  type input = Lexer.token list
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

  (** Succeeds*)
  let choice (ps : 'a t list) : 'a t =
    List.fold_right ( <|> ) ps (fun _ -> None)

  let token (t : Lexer.token) : unit t = function
    | [] -> None
    | tok :: rest when tok = t -> Some ((), rest)
    | _ -> None

  (** 0 or more *)
  let many (p : 'a t) : 'a list t =
    let rec go acc input =
      match p input with
      | None -> Some (List.rev acc, input)
      | Some (x, input') -> go (x :: acc) input'
    in
    go []

  (** 1 or more *)
  let many1 (p : 'a t) : 'a list t =
    let* first = p in
    let* rest = many p in
    return (first :: rest)
end

open Parser

let parse_ident : string t = function
  | Lexer.Ident name :: rest -> Some (name, rest)
  | _ -> None

let parse_binder_name : string option t = function
  | Lexer.Underscore :: rest -> Some (None, rest)
  | Lexer.Ident name :: rest -> Some (Some name, rest)
  | _ -> None

let parse_parens (p : 'a t) : 'a t =
  let* () = token Lexer.LParen in
  let* x = p in
  let* () = token Lexer.RParen in
  return x

let rec parse_atom : raw t =
 fun input ->
  choice
    [
      parse_fst;
      parse_snd;
      parse_refl;
      parse_absurd;
      parse_sorry;
      parse_var;
      parse_type;
      parse_unit;
      parse_empty;
      parse_int;
      parse_int_lit;
      parse_pair;
      parse_unit_term;
      parse_parens parse_preterm;
    ]
    input

and parse_var : raw t =
 fun input ->
  (let* name = parse_ident in
   return (RIdent name))
    input

and parse_type : raw t = function
  | Lexer.Type :: rest -> Some (RU, rest)
  | _ -> None

and parse_unit : raw t = function
  | Lexer.Unit :: rest -> Some (RUnit, rest)
  | _ -> None

and parse_int : raw t = function
  | Lexer.Int :: rest -> Some (RInt, rest)
  | _ -> None

and parse_int_lit : raw t = function
  | Lexer.IntLit n :: rest -> Some (RIntLit n, rest)
  | _ -> None

and parse_unit_term : raw t = function
  | Lexer.LParen :: Lexer.RParen :: rest -> Some (RUnitTm, rest)
  | _ -> None

and parse_pair : raw t =
 fun input ->
  (let* () = token Lexer.LParen in
   let* a = parse_preterm in
   let* () = token Lexer.Comma in
   let* b = parse_preterm in
   let* () = token Lexer.RParen in
   return (RPair (a, b)))
    input

and parse_fst : raw t =
 fun input ->
  (let* () = token Lexer.Fst in
   let* t = parse_atom in
   return (RProj1 t))
    input

and parse_snd : raw t =
 fun input ->
  (let* () = token Lexer.Snd in
   let* t = parse_atom in
   return (RProj2 t))
    input

and parse_refl : raw t =
 fun input ->
  (let* () = token Lexer.Refl in
   let* t = parse_atom in
   return (RRefl t))
    input

and parse_absurd : raw t =
 fun input ->
  (let* () = token Lexer.Absurd in
   let* c = parse_atom in
   let* e = parse_atom in
   return (RAbsurd (c, e)))
    input

and parse_empty : raw t = function
  | Lexer.Empty :: rest -> Some (REmpty, rest)
  | _ -> None

and parse_sorry : raw t = function
  | Lexer.Sorry :: rest -> Some (RSorry, rest)
  | _ -> None

and parse_typed_binder_group : (string option list * raw) t =
 fun input ->
  (let* () = token Lexer.LParen in
   let* names = many1 parse_binder_name in
   let* () = token Lexer.Colon in
   let* ty = parse_preterm in
   let* () = token Lexer.RParen in
   return (names, ty))
    input

and parse_paren_binder_group : (string option * raw option) list t =
 fun input ->
  (let* () = token Lexer.LParen in
   let* names = many1 parse_binder_name in
   let* ty_opt =
     (let* () = token Lexer.Colon in
      let* ty = parse_preterm in
      return (Some ty))
     <|> return None
   in
   let* () = token Lexer.RParen in
   return (List.map (fun n -> (n, ty_opt)) names))
    input

and parse_lambda : raw t =
 fun input ->
  (let* () = token Lexer.Fun in
   let* paren_groups = many parse_paren_binder_group in
   let paren_binders = List.flatten paren_groups in
   let* all_binders =
     if paren_binders = [] then
       let* names = many1 parse_binder_name in
       let* ty_opt =
         (let* () = token Lexer.Colon in
          let* ty = parse_preterm in
          return (Some ty))
         <|> return None
       in
       return (List.map (fun n -> (n, ty_opt)) names)
     else
       let* bare_names = many parse_binder_name in
       return (paren_binders @ List.map (fun n -> (n, None)) bare_names)
   in
   let* () = token Lexer.Eq_gt in
   let* body = parse_preterm in
   return
     (List.fold_right
        (fun (name, ty) body -> RLam (name, ty, body))
        all_binders body))
    input

and parse_pi : raw t =
 fun input ->
  (let* names, a = parse_typed_binder_group in
   let* () = token Lexer.Arrow in
   let* b = parse_preterm in
   return (List.fold_right (fun name body -> RPi (name, a, body)) names b))
    input

and parse_sigma : raw t =
 fun input ->
  (let* names, a = parse_typed_binder_group in
   let* () = token Lexer.Times in
   let* b = parse_preterm in
   return (List.fold_right (fun name body -> RSigma (name, a, body)) names b))
    input

and parse_app : raw t =
 fun input ->
  (let* head = parse_atom in
   let* args = many parse_atom in
   return (List.fold_left (fun f a -> RApp (f, a)) head args))
    input

and parse_add_level : raw t =
 fun input ->
  (let* first = parse_app in
   let* rest =
     many
       ((let* () = token Lexer.Plus in
         let* b = parse_app in
         return (`Add b))
       <|>
       let* () = token Lexer.Minus in
       let* b = parse_app in
       return (`Sub b))
   in
   return
     (List.fold_left
        (fun acc op ->
          match op with
          | `Add b -> RAdd (acc, b)
          | `Sub b -> RSub (acc, b))
        first rest))
    input

and parse_eq_level : raw t =
 fun input ->
  (let* a = parse_add_level in
   (let* () = token Lexer.Equal in
    let* b = parse_add_level in
    return (REq (a, b)))
   <|> return a)
    input

and parse_prod_level : raw t =
 fun input ->
  (let* a = parse_eq_level in
   (let* () = token Lexer.Times in
    let* b = parse_prod_level in
    return (RProd (a, b)))
   <|> return a)
    input

and parse_arrow_level : raw t =
 fun input ->
  (let* a = parse_prod_level in
   (let* () = token Lexer.Arrow in
    let* b = parse_arrow_level in
    return (RArrow (a, b)))
   <|> return a)
    input

and parse_preterm : raw t =
 fun input ->
  choice [ parse_lambda; parse_pi; parse_sigma; parse_arrow_level ] input

and parse_def : raw_def t = function
  | Lexer.Def :: rest ->
      (let* name = parse_ident in
       let* binder_groups = many parse_typed_binder_group in
       let binders =
         List.concat_map
           (fun (names, ty) -> List.map (fun n -> (n, ty)) names)
           binder_groups
       in
       let* ret_ty_opt =
         (let* () = token Lexer.Colon in
          let* ty = parse_preterm in
          return (Some ty))
         <|> return None
       in
       let* () = token Lexer.Colon_eq in
       let* body = parse_preterm in
       let body_with_ann =
         match ret_ty_opt with
         | Some ty -> RAnn (body, ty)
         | None -> body
       in
       let full_body =
         List.fold_right
           (fun (n, ty) acc -> RLam (n, Some ty, acc))
           binders body_with_ann
       in
       return (name, full_body))
        rest
  | _ -> None

let parse_program : raw_program t = many parse_def

let token_to_string (t : Lexer.token) : string =
  match t with
  | Lexer.Ident s -> Format.sprintf "identifier '%s'" s
  | Lexer.Type -> "Type"
  | Lexer.Unit -> "Unit"
  | Lexer.Empty -> "Empty"
  | Lexer.Def -> "def"
  | Lexer.Colon -> ":"
  | Lexer.Colon_eq -> ":="
  | Lexer.Eq_gt -> "=>"
  | Lexer.Arrow -> "→"
  | Lexer.Equal -> "="
  | Lexer.Comma -> ","
  | Lexer.LParen -> "("
  | Lexer.RParen -> ")"
  | Lexer.Fst -> "fst"
  | Lexer.Snd -> "snd"
  | Lexer.Refl -> "refl"
  | Lexer.Absurd -> "absurd"
  | Lexer.Sorry -> "sorry"
  | Lexer.Fun -> "fun"
  | Lexer.Times -> "×"
  | Lexer.Plus -> "+"
  | Lexer.Minus -> "-"
  | Lexer.Let -> "let"
  | Lexer.Int -> "Int"
  | Lexer.Underscore -> "_"
  | Lexer.IntLit n -> Format.sprintf "%d" n

let parse (input : Lexer.token list) : raw_program =
  match parse_program input with
  | None ->
      let msg =
        match input with
        | [] -> "Unexpected end of input"
        | t :: _ -> Format.sprintf "Unexpected token: %s" (token_to_string t)
      in
      raise (Parse_error msg)
  | Some (x, []) -> x
  | Some (_, remaining) -> raise (Tokens_remaining remaining)
