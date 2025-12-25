open Lexer

exception Syntax_error of string

type prec =
  | PrecMin
  | PrecLet
  | PrecFun
  | PrecPi
  | PrecEq
  | PrecAdd
  | PrecApp
  | PrecMax
[@@deriving compare]

open struct
  type input = token list
  type 'a t = input -> ('a * input) option

  let return (x : 'a) : 'a t = fun input -> Some (x, input)
  let fail : 'a t = fun _ -> None

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

  let choice (ps : 'a t list) : 'a t = List.fold_right ( <|> ) ps fail

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

(* ========== Pratt Parser Infrastructure ========== *)

type leading_parser = Raw_syntax.t t

(* prec, lhs_prec, and left operand, returns combined expression *)
type trailing_parser = prec -> prec -> Raw_syntax.t -> Raw_syntax.t t

(* Try all leading parsers in order until one succeeds *)

(* Try all trailing parsers in order until one succeeds *)

let parse_ident : string t = function
  | Ident name :: rest -> Some (name, rest)
  | _ -> None

let parse_binder_name : string option t = function
  | Underscore :: rest -> Some (None, rest)
  | Ident name :: rest -> Some (Some name, rest)
  | _ -> None

let parse_sorry : Raw_syntax.t t = function
  | Sorry :: rest -> Some (Raw_syntax.Sorry, rest)
  | _ -> None

let parse_var : Raw_syntax.t t =
  let* name = parse_ident in
  return (Raw_syntax.Ident name)

let parse_type : Raw_syntax.t t = function
  | Type :: rest -> Some (Raw_syntax.U, rest)
  | _ -> None

let parse_int_lit : Raw_syntax.t t = function
  | NatLit n :: rest -> Some (Raw_syntax.NatLit n, rest)
  | _ -> None

let parse_unit : Raw_syntax.t t = function
  | LParen :: RParen :: rest -> Some (Raw_syntax.Ident "Unit.unit", rest)
  | _ -> None

let rec pratt_parser (min_prec : prec) : Raw_syntax.t t =
  let leading_parsers =
    [
      (PrecMax, parse_pi_leading);
      (PrecMax, parse_sigma_leading);
      (PrecMax, parse_atom_leading);
      (PrecFun, parse_lambda_leading);
      (PrecLet, parse_let_leading);
    ]
  in
  let trailing_parsers =
    [
      (PrecApp, PrecMax, parse_app_trailing);
      (PrecAdd, PrecAdd, parse_add_trailing);
      (PrecEq, PrecEq, parse_eq_trailing);
      (PrecPi, PrecPi, parse_prod_trailing);
      (PrecPi, PrecPi, parse_arrow_trailing);
    ]
  in

  let leading_parsers =
    List.filter_map
      (fun (prec, parser) ->
        if compare_prec prec min_prec >= 0 then
          Some parser
        else
          None)
      leading_parsers
  in

  let* left = choice leading_parsers in

  let try_trailing_parsers (left : Raw_syntax.t) : Raw_syntax.t t =
    let trailing_parsers =
      List.filter_map
        (fun (prec, lhs_prec, parser) ->
          if compare_prec prec min_prec >= 0 then
            Some (parser prec lhs_prec left)
          else
            None)
        trailing_parsers
    in
    choice trailing_parsers
  in

  let rec parse_trailing_loop (left : Raw_syntax.t) : Raw_syntax.t t =
    let* left_opt = optional (try_trailing_parsers left) in
    match left_opt with
    | Some new_left -> parse_trailing_loop new_left
    | None -> return left
  in
  parse_trailing_loop left

and parse_pair : Raw_syntax.t t =
 fun input ->
  (let* () = token LParen in
   let* a = pratt_parser PrecMin in
   let* () = token Comma in
   let* b = pratt_parser PrecMin in
   let* () = token RParen in
   return (Raw_syntax.Pair (a, b)))
    input

and parse_ann_or_parens : Raw_syntax.t t =
 fun input ->
  (let* () = token LParen in
   let* e = pratt_parser PrecMin in
   (let* () = token Colon in
    let* ty = pratt_parser PrecMin in
    let* () = token RParen in
    return (Raw_syntax.Ann (e, ty)))
   <|>
   let* () = token RParen in
   return e)
    input

(* Leading parsers for atoms *)
and parse_atom_leading : leading_parser =
 fun input ->
  choice
    [
      parse_sorry;
      parse_var;
      parse_type;
      parse_int_lit;
      parse_pair;
      parse_unit;
      parse_ann_or_parens;
    ]
    input

and parse_typed_binder_group : Raw_syntax.typed_binder_group t =
 fun input ->
  (let* () = token LParen in
   let* names = many1 parse_binder_name in
   let* () = token Colon in
   let* ty = pratt_parser PrecMin in
   let* () = token RParen in
   return (names, ty))
    input

and parse_untyped_binder : string t =
 fun input ->
  (let* name = parse_binder_name in
   return
     (match name with
     | Some name -> name
     | None -> "_"))
    input

and parse_binder_group : Raw_syntax.binder_group t =
 fun input ->
  ((let* group = parse_typed_binder_group in
    return (Raw_syntax.Typed group))
  <|> let* name = parse_untyped_binder in
      return (Raw_syntax.Untyped name))
    input

and parse_lambda_leading : leading_parser =
 fun input ->
  (let* () = token Fun in
   let* binder_groups = many1 parse_binder_group in
   let* () = token Eq_gt in
   let* body = pratt_parser PrecMin in
   return (Raw_syntax.Lam (binder_groups, body)))
    input

and parse_let_leading : leading_parser =
 fun input ->
  (let* () = token Let in
   let* name = parse_ident in
   let* ty_opt =
     optional
       (let* () = token Colon in
        pratt_parser PrecMin)
   in
   let* () = token Colon_eq in
   let* e = pratt_parser PrecMin in
   let* () = token Semicolon in
   let* body = pratt_parser PrecMin in
   return (Raw_syntax.Let (name, ty_opt, e, body)))
    input

(* Leading parser for Pi *)
and parse_pi_leading : leading_parser =
 fun input ->
  (let* group = parse_typed_binder_group in
   let* () = token Arrow in
   let* b = pratt_parser PrecPi in
   return (Raw_syntax.Pi (group, b)))
    input

(* Leading parser for Sigma *)
and parse_sigma_leading : leading_parser =
 fun input ->
  (let* group = parse_typed_binder_group in
   let* () = token Times in
   let* b = pratt_parser PrecPi in
   return (Raw_syntax.Sigma (group, b)))
    input

(* Trailing parser for application *)
and parse_app_trailing : trailing_parser =
 fun _prec _lhs_prec left input ->
  (* Parse an argument (atom or lambda/let) *)
  match parse_atom_leading input with
  | Some (arg, input') -> Some (Raw_syntax.App (left, arg), input')
  | None -> (
      (* Try lambda or let *)
      match parse_lambda_leading input with
      | Some (arg, input') -> Some (Raw_syntax.App (left, arg), input')
      | None -> (
          match parse_let_leading input with
          | Some (arg, input') -> Some (Raw_syntax.App (left, arg), input')
          | None -> None))

(* Trailing parser for addition *)
and parse_add_trailing : trailing_parser =
 fun _prec _lhs_prec left input ->
  ((let* () = token Plus in
    let* b = pratt_parser PrecAdd in
    return (Raw_syntax.Add (left, b)))
  <|>
  let* () = token Minus in
  let* b = pratt_parser PrecAdd in
  return (Raw_syntax.Sub (left, b)))
  |> fun p -> p input

(* Trailing parser for equality *)
and parse_eq_trailing : trailing_parser =
 fun _prec _lhs_prec left input ->
  (let* () = token Equal in
   let* b = pratt_parser PrecEq in
   return (Raw_syntax.Eq (left, b)))
  |> fun p -> p input

(* Trailing parser for product *)
and parse_prod_trailing : trailing_parser =
 fun _prec _lhs_prec left input ->
  (let* () = token Times in
   let* b = pratt_parser PrecPi in
   return (Raw_syntax.Prod (left, b)))
  |> fun p -> p input

(* Trailing parser for arrow *)
and parse_arrow_trailing : trailing_parser =
 fun _prec _lhs_prec left input ->
  (let* () = token Arrow in
   let* b = pratt_parser PrecPi in
   return (Raw_syntax.Arrow (left, b)))
  |> fun p -> p input

and parse_preterm : Raw_syntax.t t = fun input -> pratt_parser PrecMin input

(* ========== Top level ========== *)

let parse_params : Raw_syntax.typed_binder_group list t =
  many parse_typed_binder_group

let parse_constructor : Raw_syntax.constructor t =
  let* () = token Pipe in
  let* name = parse_ident in
  let* params = parse_params in
  let* ty_opt =
    optional
      (let* () = token Colon in
       parse_preterm)
  in
  return { Raw_syntax.name; params; ty_opt }

let parse_inductive : Raw_syntax.item t =
  let* () = token Inductive in
  let* name = parse_ident in
  let* params = parse_params in
  let* ty_opt =
    optional
      (let* () = token Colon in
       parse_preterm)
  in
  let* () = token Where in
  let* ctors = many parse_constructor in
  return (Raw_syntax.Inductive { name; params; ty_opt; ctors })

let parse_field : Raw_syntax.field t =
  let* () = token LParen in
  let* name = parse_ident in
  if String.contains name '.' then
    raise (Syntax_error "Structure field names must be atomic");
  let* args = parse_params in
  let* () = token Colon in
  let* ty = parse_preterm in
  let* () = token RParen in
  return { Raw_syntax.name; binders = args; ty }

let parse_structure : Raw_syntax.item t =
  let* () = token Structure in
  let* name = parse_ident in
  let* params = parse_params in
  let* ty_opt =
    optional
      (let* () = token Colon in
       parse_preterm)
  in
  let* () = token Where in
  let* fields = many parse_field in
  return (Raw_syntax.Structure { name; params; ty_opt; fields })

let parse_def_body :
    (Raw_syntax.typed_binder_group list * Raw_syntax.t option * Raw_syntax.t) t
    =
  let* params = parse_params in
  let* ret_ty_opt =
    optional
      (let* () = token Colon in
       parse_preterm)
  in
  let* () = token Colon_eq in
  let* body = parse_preterm in
  return (params, ret_ty_opt, body)

let parse_def : Raw_syntax.item t =
  let* () = token Def in
  let* name = parse_ident in
  let* params, ty_opt, body = parse_def_body in
  return (Raw_syntax.Def { name; params; ty_opt; body })

let parse_example : Raw_syntax.item t =
  let* () = token Example in
  let* params, ty_opt, body = parse_def_body in
  return (Raw_syntax.Example { params; ty_opt; body })

let parse_axiom : Raw_syntax.item t =
  let* () = token Axiom in
  let* name = parse_ident in
  let* params = parse_params in
  let* () = token Colon in
  let* ty = parse_preterm in
  return (Raw_syntax.Axiom { name; params; ty })

let parse_single_item : Raw_syntax.item t =
  choice
    [
      parse_structure;
      parse_inductive;
      parse_def;
      parse_example;
      parse_axiom;
      (let* () = token Import in
       let* name = parse_ident in
       return (Raw_syntax.Import { module_name = name }));
    ]

let parse_program : Raw_syntax.program t =
 fun input -> many parse_single_item input

let parse (input : token list) : Raw_syntax.program =
  match parse_program input with
  | None ->
      let msg =
        match input with
        | [] -> "Unexpected end of input"
        | t :: _ -> Format.asprintf "Unexpected token: %a" pp_token t
      in
      raise (Syntax_error msg)
  | Some (x, []) -> x
  | Some (_, remaining) ->
      raise
        (Syntax_error
           (Format.asprintf "Syntax error: %a"
              (Format.pp_print_list ~pp_sep:Format.pp_print_space pp_token)
              (List.take 10 remaining)))
