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
    | Some _ as result -> result
    | None -> p2 input

  (** Succeeds on the first one *)
  let choice (ps : 'a t list) : 'a t =
    List.fold_right ( <|> ) ps (fun _ -> None)

  let token (t : token) : unit t = function
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

let parse_ann_or_parens (p : raw t) : raw t =
  let* () = token LParen in
  let* e = p in
  (let* () = token Colon in
   let* ty = p in
   let* () = token RParen in
   return (RAnn (e, ty)))
  <|>
  let* () = token RParen in
  return e

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
      parse_ann_or_parens parse_preterm;
    ]
    input

and parse_var : raw t =
 fun input ->
  (let* name = parse_ident in
   return (RIdent name))
    input

and parse_type : raw t = function
  | Type :: rest -> Some (RU, rest)
  | _ -> None

and parse_unit : raw t = function
  | Unit :: rest -> Some (RUnit, rest)
  | _ -> None

and parse_int : raw t = function
  | Int :: rest -> Some (RInt, rest)
  | _ -> None

and parse_int_lit : raw t = function
  | IntLit n :: rest -> Some (RIntLit n, rest)
  | _ -> None

and parse_unit_term : raw t = function
  | LParen :: RParen :: rest -> Some (RUnitTm, rest)
  | _ -> None

and parse_pair : raw t =
 fun input ->
  (let* () = token LParen in
   let* a = parse_preterm in
   let* () = token Comma in
   let* b = parse_preterm in
   let* () = token RParen in
   return (RPair (a, b)))
    input

and parse_fst : raw t =
 fun input ->
  (let* () = token Fst in
   let* t = parse_atom in
   return (RProj1 t))
    input

and parse_snd : raw t =
 fun input ->
  (let* () = token Snd in
   let* t = parse_atom in
   return (RProj2 t))
    input

and parse_refl : raw t =
 fun input ->
  (let* () = token Refl in
   let* t = parse_atom in
   return (RRefl t))
    input

and parse_absurd : raw t =
 fun input ->
  (let* () = token Absurd in
   let* e = parse_atom in
   return (RAbsurd e))
    input

and parse_empty : raw t = function
  | Empty :: rest -> Some (REmpty, rest)
  | _ -> None

and parse_sorry : raw t = function
  | Sorry :: rest -> Some (RSorry, rest)
  | _ -> None

and parse_typed_binder_group : (string option list * raw) t =
 fun input ->
  (let* () = token LParen in
   let* names = many1 parse_binder_name in
   let* () = token Colon in
   let* ty = parse_preterm in
   let* () = token RParen in
   return (names, ty))
    input

and parse_paren_binder_group : (string option * raw option) list t =
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

and parse_lambda : raw t =
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
   return (RLam (all_binders, body)))
    input

and parse_let : raw t =
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
   return (RLet (name, ty_opt, e, body)))
    input

and parse_pi : raw t =
 fun input ->
  (let* group = parse_typed_binder_group in
   let* () = token Arrow in
   let* b = parse_preterm in
   return (RPi (group, b)))
    input

and parse_sigma : raw t =
 fun input ->
  (let* group = parse_typed_binder_group in
   let* () = token Times in
   let* b = parse_preterm in
   return (RSigma (group, b)))
    input

and parse_app : raw t =
 fun input ->
  (let* head = parse_atom in
   let* args = many parse_atom in
   let* final = optional (parse_lambda <|> parse_let) in
   let all_args =
     match final with
     | Some e -> args @ [ e ]
     | None -> args
   in
   return (List.fold_left (fun f a -> RApp (f, a)) head all_args))
    input

and parse_add_level : raw t =
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
          | `Add b -> RAdd (acc, b)
          | `Sub b -> RSub (acc, b))
        first rest))
    input

and parse_eq_rhs : raw t =
 fun input -> choice [ parse_lambda; parse_let; parse_add_level ] input

and parse_eq_level : raw t =
 fun input ->
  (let* a = parse_add_level in
   (let* () = token Equal in
    let* b = parse_eq_rhs in
    return (REq (a, b)))
   <|> return a)
    input

and parse_prod_level : raw t =
 fun input ->
  (parse_sigma
  <|>
  let* a = parse_eq_level in
  (let* () = token Times in
   let* b = parse_prod_level in
   return (RProd (a, b)))
  <|> return a)
    input

and parse_arrow_level : raw t =
 fun input ->
  (parse_pi
  <|>
  let* a = parse_prod_level in
  (let* () = token Arrow in
   let* b = parse_arrow_level in
   return (RArrow (a, b)))
  <|> return a)
    input

and parse_preterm : raw t =
 fun input ->
  choice
    [ parse_lambda; parse_let; parse_pi; parse_sigma; parse_arrow_level ]
    input

let rec parse_item : raw_item t =
 fun input ->
  ((let* () = token Def in
    let* name = parse_ident in
    let* body = parse_def_body in
    return (RDef (name, body)))
  <|>
  let* () = token Example in
  let* body = parse_def_body in
  return (RExample body))
    input

and parse_def_body : raw t =
 fun input ->
  (let* binder_groups = many parse_typed_binder_group in
   let binders : binder list =
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
     | Some ty -> RAnn (body, ty)
     | None -> body
   in
   let full_body =
     if binders = [] then
       body_with_ann
     else
       RLam (binders, body_with_ann)
   in
   return full_body)
    input

let parse_program : raw_program t = many parse_item

let parse (input : token list) : raw_program =
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
