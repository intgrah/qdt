open Syntax
open Lexer

exception Parse_error of string
exception Tokens_remaining of token list

module Parser = struct
  type input = token list
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
    | Some a -> Some a
    | None -> p2 input

  let choice (ps : 'a t list) : 'a t =
    List.fold_right ( <|> ) ps (fun _ -> None)

  let token (t : token) : unit t = function
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

  let many1 (p : 'a t) : 'a list t =
    let* first = p in
    let* rest = many p in
    return (first :: rest)

  let optional (p : 'a t) : 'a option t =
   fun input ->
    match p input with
    | None -> Some (None, input)
    | Some (x, input') -> Some (Some x, input')
end

open Parser

let parse_ident : string t = function
  | Ident name :: rest -> Some (name, rest)
  | _ -> None

let parse_binder_name : string option t = function
  | Underscore :: rest -> Some (None, rest)
  | Ident name :: rest -> Some (Some name, rest)
  | _ -> None

let parse_ann_or_parens (p : Raw.t t) : Raw.t t =
  let* () = token LParen in
  let* e = p in
  (let* () = token Colon in
   let* ty = p in
   let* () = token RParen in
   return (Raw.Ann (e, ty)))
  <|>
  let* () = token RParen in
  return e

let rec parse_atom : Raw.t t =
 fun input ->
  choice
    [
      parse_sorry;
      parse_var;
      parse_type;
      parse_int_lit;
      parse_pair;
      parse_unit_term;
      parse_ann_or_parens parse_preterm;
    ]
    input

and parse_var : Raw.t t =
 fun input ->
  (let* name = parse_ident in
   return (Raw.Ident name))
    input

and parse_type : Raw.t t = function
  | Type :: rest -> Some (Raw.U, rest)
  | _ -> None

and parse_int_lit : Raw.t t = function
  | IntLit n :: rest -> Some (Raw.IntLit n, rest)
  | _ -> None

and parse_unit_term : Raw.t t = function
  | LParen :: RParen :: rest -> Some (Raw.Ident "Unit.unit", rest)
  | _ -> None

and parse_pair : Raw.t t =
 fun input ->
  (let* () = token LParen in
   let* a = parse_preterm in
   let* () = token Comma in
   let* b = parse_preterm in
   let* () = token RParen in
   return (Raw.Pair (a, b)))
    input

and parse_sorry : Raw.t t = function
  | Sorry :: rest -> Some (Raw.Sorry, rest)
  | _ -> None

and parse_typed_binder_group : Raw.binder_group t =
 fun input ->
  (let* () = token LParen in
   let* names = many1 parse_binder_name in
   let* () = token Colon in
   let* ty = parse_preterm in
   let* () = token RParen in
   return (names, ty))
    input

and parse_paren_binder_group : Raw.binder list t =
 fun input ->
  (let* () = token LParen in
   let* names = many1 parse_binder_name in
   let* ty_opt =
     optional
       (let* () = token Colon in
        parse_preterm)
   in
   let* () = token RParen in
   return (List.map (fun n -> (n, ty_opt)) names))
    input

and parse_lambda : Raw.t t =
 fun input ->
  (let* () = token Fun in
   let* paren_groups = many parse_paren_binder_group in
   let paren_binders = List.flatten paren_groups in
   let* all_binders =
     if paren_binders = [] then
       let* names = many1 parse_binder_name in
       let* ty_opt =
         optional
           (let* () = token Colon in
            parse_preterm)
       in
       return (List.map (fun n -> (n, ty_opt)) names)
     else
       let* bare_names = many parse_binder_name in
       return (paren_binders @ List.map (fun n -> (n, None)) bare_names)
   in
   let* () = token Eq_gt in
   let* body = parse_preterm in
   return (Raw.Lam (all_binders, body)))
    input

and parse_let : Raw.t t =
 fun input ->
  (let* () = token Let in
   let* name = parse_ident in
   let* ty_opt =
     optional
       (let* () = token Colon in
        parse_preterm)
   in
   let* () = token Colon_eq in
   let* e = parse_preterm in
   let* () = token Semicolon in
   let* body = parse_preterm in
   return (Raw.Let (name, ty_opt, e, body)))
    input

and parse_pi : Raw.t t =
 fun input ->
  (let* group = parse_typed_binder_group in
   let* () = token Arrow in
   let* b = parse_preterm in
   return (Raw.Pi (group, b)))
    input

and parse_sigma : Raw.t t =
 fun input ->
  (let* group = parse_typed_binder_group in
   let* () = token Times in
   let* b = parse_preterm in
   return (Raw.Sigma (group, b)))
    input

and parse_app : Raw.t t =
 fun input ->
  (let* head = parse_atom in
   let* args = many parse_atom in
   let* final = optional (parse_lambda <|> parse_let) in
   let all_args =
     match final with
     | Some e -> args @ [ e ]
     | None -> args
   in
   return (List.fold_left (fun f a -> Raw.App (f, a)) head all_args))
    input

and parse_add_level : Raw.t t =
 fun input ->
  (let* first = parse_app in
   let* rest =
     many
       ((let* () = token Plus in
         let* b = parse_app in
         return (`Add b))
       <|>
       let* () = token Minus in
       let* b = parse_app in
       return (`Sub b))
   in
   return
     (List.fold_left
        (fun acc op ->
          match op with
          | `Add b -> Raw.Add (acc, b)
          | `Sub b -> Raw.Sub (acc, b))
        first rest))
    input

and parse_eq_rhs : Raw.t t =
 fun input -> choice [ parse_lambda; parse_let; parse_add_level ] input

and parse_eq_level : Raw.t t =
 fun input ->
  (let* a = parse_add_level in
   (let* () = token Equal in
    let* b = parse_eq_rhs in
    return (Raw.Eq (a, b)))
   <|> return a)
    input

and parse_prod_level : Raw.t t =
 fun input ->
  (parse_sigma
  <|>
  let* a = parse_eq_level in
  (let* () = token Times in
   let* b = parse_prod_level in
   return (Raw.Prod (a, b)))
  <|> return a)
    input

and parse_arrow_level : Raw.t t =
 fun input ->
  (parse_pi
  <|>
  let* a = parse_prod_level in
  (let* () = token Arrow in
   let* b = parse_arrow_level in
   return (Raw.Arrow (a, b)))
  <|> return a)
    input

and parse_preterm : Raw.t t =
 fun input ->
  choice
    [ parse_lambda; parse_let; parse_pi; parse_sigma; parse_arrow_level ]
    input

and parse_constructor : Raw.constructor t =
 fun input ->
  (let* () = token Pipe in
   let* name = parse_ident in
   let* params = many parse_paren_binder_group in
   let params = List.flatten params in
   let* ty_opt =
     optional
       (let* () = token Colon in
        parse_preterm)
   in
   return { Raw.name; params; ty = ty_opt })
    input

and parse_inductive : Raw.item t =
 fun input ->
  (let* () = token Inductive in
   let* name = parse_ident in
   let* params = many parse_typed_binder_group in
   let* ty_opt =
     optional
       (let* () = token Colon in
        parse_preterm)
   in
   let* () = token Where in
   let* ctors = many parse_constructor in
   return (Raw.Inductive { name; params; ty = ty_opt; ctors }))
    input

and parse_field : Raw.field t =
 fun input ->
  (let* () = token LParen in
   let* name = parse_ident in
   if String.contains name '.' then
     raise (Parse_error "Structure field names must be atomic");
   let* args = many parse_typed_binder_group in
   let* () = token Colon in
   let* ty = parse_preterm in
   let* () = token RParen in
   return { Raw.name; binders = args; ty })
    input

and parse_structure : Raw.item t =
 fun input ->
  (let* () = token Structure in
   let* name = parse_ident in
   let* params = many parse_typed_binder_group in
   let* ty_opt =
     optional
       (let* () = token Colon in
        parse_preterm)
   in
   let* () = token Where in
   let* fields = many parse_field in
   return (Raw.Structure { name; params; ty = ty_opt; fields }))
    input

let rec parse_single_item : Raw.item t =
 fun input ->
  choice
    [
      parse_structure;
      parse_inductive;
      (let* () = token Def in
       let* name = parse_ident in
       let* body = parse_def_body in
       return (Raw.Def { name; body }));
      (let* () = token Example in
       let* body = parse_def_body in
       return (Raw.Example { body }));
      (let* () = token Import in
       let* name = parse_ident in
       return (Raw.Import { module_name = name }));
    ]
    input

and parse_def_body : Raw.t t =
 fun input ->
  (let* binder_groups = many parse_typed_binder_group in
   let binders : Raw.binder list =
     List.concat_map
       (fun (names, ty) -> List.map (fun n -> (n, Some ty)) names)
       binder_groups
   in
   let* ret_ty_opt =
     optional
       (let* () = token Colon in
        parse_preterm)
   in
   let* () = token Colon_eq in
   let* body = parse_preterm in
   let body_with_ann =
     match ret_ty_opt with
     | Some ty -> Raw.Ann (body, ty)
     | None -> body
   in
   let full_body =
     if binders = [] then
       body_with_ann
     else
       Raw.Lam (binders, body_with_ann)
   in
   return full_body)
    input

let parse_program : Raw.program t = fun input -> many parse_single_item input

let parse (input : token list) : Raw.program =
  match parse_program input with
  | None ->
      let msg =
        match input with
        | [] -> "Unexpected end of input"
        | t :: _ -> Format.asprintf "Unexpected token: %a" pp_token t
      in
      raise (Parse_error msg)
  | Some (x, []) -> x
  | Some (_, remaining) -> raise (Tokens_remaining remaining)
