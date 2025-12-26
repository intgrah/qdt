open Cst
open Syntax

type parse_error = {
  msg : string;
  pos : position;
}

exception Syntax_error of parse_error

(* ========== Positions and state ========== *)

type rune = {
  ch : Uchar.t;
  line : int;
  col : int;
}

type state = {
  dec : rune array;
  idx : int;
}

let get_pos (st : state) : Syntax.position =
  if st.idx < Array.length st.dec then
    let r = st.dec.(st.idx) in
    { offset = st.idx; line = r.line; column = r.col }
  else if Array.length st.dec = 0 then
    { offset = 0; line = 1; column = 1 }
  else
    let r = st.dec.(Array.length st.dec - 1) in
    { offset = Array.length st.dec; line = r.line; column = r.col + 1 }

let decode_source (s : string) : rune array =
  let byte_len = String.length s in
  let rec loop byte_idx line col cp acc =
    if byte_idx >= byte_len then
      let runes = Array.of_list (List.rev acc) in
      runes
    else
      let dec = String.get_utf_8_uchar s byte_idx in
      let len_bytes = Uchar.utf_decode_length dec in
      let ch = Uchar.utf_decode_uchar dec in
      let pos : Syntax.position = { offset = cp; line; column = col } in
      if not (Uchar.utf_decode_is_valid dec) then
        raise (Syntax_error { msg = "Invalid UTF-8 sequence"; pos })
      else
        let rune = { ch; line; col } in
        let line', col' =
          if Uchar.to_int ch = Char.code '\n' then
            (line + 1, 1)
          else
            (line, col + 1)
        in
        loop (byte_idx + len_bytes) line' col' (cp + 1) (rune :: acc)
  in
  loop 0 1 1 0 []

let init_state (s : string) : state = { dec = decode_source s; idx = 0 }

module Parser = struct
  type 'a t = state -> ('a * state, parse_error) result

  let pure (x : 'a) : 'a t = fun st -> Ok (x, st)

  let bind (m : 'a t) (f : 'a -> 'b t) : 'b t =
   fun st ->
    match m st with
    | Ok (a, st') -> f a st'
    | Error _ as e -> e

  let ( let* ) = bind
  let ( >>= ) = bind
  let ( >> ) p f = p >>= fun () -> f

  let ( let+ ) (f : state -> 'a) (k : 'a -> 'b t) : 'b t =
    (fun st -> Ok (f st, st)) >>= k

  let alt p1 p2 =
   fun st ->
    match p1 st with
    | Ok _ as r -> r
    | Error _ -> p2 st

  let ( <|> ) = alt

  let fail msg : 'a t =
    let+ pos = get_pos in
    fun _ -> Error { msg; pos }

  let lift2 f p1 p2 =
    let* x1 = p1 in
    let* x2 = p2 in
    pure (f x1 x2)

  let optional p =
   fun st ->
    match p st with
    | Ok (x, st') -> Ok (Some x, st')
    | Error _ -> Ok (None, st)

  let rec many (p : 'a t) : 'a list t =
    (let* x = p in
     let* xs = many p in
     pure (x :: xs))
    <|> pure []

  let many1 p = lift2 List.cons p (many p)

  let rec choice : 'a t list -> 'a t -> 'a t =
   fun ps fail ->
    match ps with
    | [] -> fail
    | p :: ps -> alt p (choice ps fail)
end

open Parser

let is_eof st = st.idx >= Array.length st.dec

let get_cp st =
  if is_eof st then
    None
  else
    Some (Uchar.to_int st.dec.(st.idx).ch)

let advance_char : unit Parser.t =
 fun st ->
  if is_eof st then
    Error { msg = "Unexpected end of input"; pos = get_pos st }
  else
    Ok ((), { st with idx = st.idx + 1 })

let rec advance_n (n : int) : unit Parser.t =
  if n = 0 then
    pure ()
  else
    advance_char >> advance_n (n - 1)

let rec skip_line : unit Parser.t =
 fun st ->
  (let+ eof = is_eof in
   if eof then
     pure ()
   else
     let+ cp = get_cp in
     match cp with
     | Some cp when cp = Char.code '\n' -> advance_char
     | _ -> advance_char >> skip_line)
    st

let rec ws : unit Parser.t =
 fun st ->
  (let+ eof = is_eof in
   if eof then
     pure ()
   else
     let+ cp = get_cp in
     let+ cp_next = fun st -> get_cp { st with idx = st.idx + 1 } in
     match (cp, cp_next) with
     | Some cp, _
       when cp = Char.code ' '
            || cp = Char.code '\t'
            || cp = Char.code '\r'
            || cp = Char.code '\n' ->
         advance_char >> ws
     | Some 0x2D, Some 0x2D (* '--' *) ->
         let* () = advance_n 2 in
         let* () = skip_line in
         ws
     | Some 0x2F, Some 0x2D (* '/-' *) ->
         let rec skip_block depth : unit Parser.t =
           let+ eof = is_eof in
           if eof then
             fail "Unterminated comment"
           else
             let+ cp = get_cp in
             let+ cp_next = fun st -> get_cp { st with idx = st.idx + 1 } in
             match (cp, cp_next) with
             | Some 0x2F, Some 0x2D -> advance_n 2 >> skip_block (depth + 1)
             | Some 0x2D, Some 0x2F -> advance_n 2 >> skip_block (depth - 1)
             | _ -> advance_char >> skip_block depth
         in
         advance_n 2 >> skip_block 0 >> ws
     | _ -> pure ())
    st

let is_ident_char cp =
  (cp >= Char.code 'A' && cp <= Char.code 'Z')
  || (cp >= Char.code 'a' && cp <= Char.code 'z')
  || (cp >= Char.code '0' && cp <= Char.code '9')
  || cp = Char.code '_'
  || cp = Char.code '\''
  || cp = Char.code '.'

let is_ident_start cp =
  (cp >= Char.code 'A' && cp <= Char.code 'Z')
  || (cp >= Char.code 'a' && cp <= Char.code 'z')
  || cp = Char.code '_'
  || cp = Char.code '\''

let read_ident : string Parser.t =
  let+ cp = get_cp in
  match cp with
  | None -> fail "expected identifier"
  | Some cp ->
      if not (is_ident_start cp) then
        fail "expected identifier"
      else
        let buf = Buffer.create 16 in
        Buffer.add_utf_8_uchar buf (Uchar.of_int cp);
        let* () = advance_char in
        let rec loop_aux () : string Parser.t =
          let+ eof = is_eof in
          if eof then
            pure (Buffer.contents buf)
          else
            let+ cp' = get_cp in
            match cp' with
            | Some cp_val when is_ident_char cp_val ->
                Buffer.add_utf_8_uchar buf (Uchar.of_int cp_val);
                let* () = advance_char in
                loop_aux ()
            | _ -> pure (Buffer.contents buf)
        in
        loop_aux ()

let get_start_pos : Cst.t -> Syntax.position = function
  | Missing src
  | U src
  | Sorry src -> (
      match src with
      | None -> { offset = 0; line = 0; column = 0 }
      | Some { start_pos; _ } -> start_pos)
  | Ident (src, _)
  | App (src, _, _)
  | Lam (src, _, _)
  | Pi (src, _, _)
  | Arrow (src, _, _)
  | Let (src, _, _, _, _)
  | Sigma (src, _, _)
  | Prod (src, _, _)
  | Pair (src, _, _)
  | Eq (src, _, _)
  | NatLit (src, _)
  | Add (src, _, _)
  | Sub (src, _, _)
  | Mul (src, _, _)
  | Ann (src, _, _) -> (
      match src with
      | None -> { offset = 0; line = 0; column = 0 }
      | Some { start_pos; _ } -> start_pos)

let decode_string_to_uchars (s : string) : Uchar.t list =
  let rec loop byte_idx acc =
    if byte_idx >= String.length s then
      List.rev acc
    else
      let dec = String.get_utf_8_uchar s byte_idx in
      if not (Uchar.utf_decode_is_valid dec) then
        failwith (Format.sprintf "Invalid UTF-8 in string: %s" s)
      else
        let uchar = Uchar.utf_decode_uchar dec in
        let len_bytes = Uchar.utf_decode_length dec in
        loop (byte_idx + len_bytes) (uchar :: acc)
  in
  loop 0 []

let str (s : string) : unit Parser.t =
  let expected = decode_string_to_uchars s in
  let rec loop expected_list : unit Parser.t =
    match expected_list with
    | [] -> pure ()
    | expected_uchar :: rest ->
        let+ eof = is_eof in
        if eof then
          fail (Format.sprintf "unexpected end of input, expected '%s'" s)
        else
          let+ uchar = fun st -> st.dec.(st.idx).ch in
          if Uchar.equal uchar expected_uchar then
            advance_char >> loop rest
          else
            fail (Format.sprintf "expected '%s'" s)
  in
  ws >> loop expected

let keyword (kw : string) : unit Parser.t = str kw
let arrow : unit Parser.t = str "->" <|> str "→"
let times : unit Parser.t = str "×"

let parse_nat : int Parser.t =
  let* () = ws in
  let+ eof = is_eof in
  if eof then
    fail "expected numeral"
  else
    let+ cp = get_cp in
    match cp with
    | Some cp when cp >= Char.code '0' && cp <= Char.code '9' ->
        let rec loop_aux acc : int Parser.t =
          let+ cp = get_cp in
          match cp with
          | Some d when d >= Char.code '0' && d <= Char.code '9' ->
              let* () = advance_char in
              loop_aux ((acc * 10) + (d - Char.code '0'))
          | _ -> pure acc
        in
        let* () = advance_char in
        loop_aux (cp - Char.code '0')
    | _ -> fail "expected numeral"

let parse_ident : (Syntax.src * string) Parser.t =
  let* () = ws in
  let+ start_pos = get_pos in
  let* name = read_ident in
  let+ end_pos = get_pos in
  pure (Some { start_pos; end_pos }, name)

type prec =
  | PrecMin
  | PrecLet
  | PrecFun
  | PrecPi
  | PrecEq
  | PrecAddL
  | PrecAddR
  | PrecMulL
  | PrecMulR
  | PrecApp
  | PrecMax
[@@deriving compare]

let parse_binder_name : string option Parser.t =
  let* _src, name = parse_ident in
  if name = "_" then
    pure None
  else
    pure (Some name)

let rec parse_typed_binder_group : Cst.typed_binder_group Parser.t =
 fun st ->
  (let* () = ws in
   let+ start_pos = get_pos in
   let* () = str "(" in
   let* names = many1 parse_binder_name in
   let* () = str ":" in
   let* ty = parse_preterm in
   let* () = str ")" in
   let+ end_pos = get_pos in
   pure (Some { start_pos; end_pos }, names, ty))
    st

and parse_binder_group : Cst.binder_group Parser.t =
 fun st ->
  ((let* group = parse_typed_binder_group in
    pure (Cst.Typed group))
  <|> let+ start_pos = get_pos in
      let* name = parse_binder_name in
      let+ end_pos = get_pos in
      pure (Cst.Untyped (Some { start_pos; end_pos }, name)))
    st

and parse_lambda_leading : Cst.t Parser.t =
 fun st ->
  (let+ start_pos = get_pos in
   let* () = keyword "fun" in
   let* binders = many1 parse_binder_group in
   let* () = keyword "=>" in
   let* body = parse_preterm in
   let+ end_pos = get_pos in
   pure (Cst.Lam (Some { start_pos; end_pos }, binders, body)))
    st

and parse_let_leading : Cst.t Parser.t =
 fun st ->
  (let+ start_pos = get_pos in
   let* () = keyword "let" in
   let* _info_name, name = parse_ident in
   let* ty_opt = optional (str ":" >> parse_preterm) in
   let* () = keyword ":=" in
   let* rhs = parse_preterm in
   let* () = str ";" in
   let* body = parse_preterm in
   let+ end_pos = get_pos in
   pure (Cst.Let (Some { start_pos; end_pos }, name, ty_opt, rhs, body)))
    st

and parse_pi_leading : Cst.t Parser.t =
 fun st ->
  (let* () = ws in
   let+ start_pos = get_pos in
   let* group = parse_typed_binder_group in
   let* () = arrow in
   let* b = pratt_parser PrecPi in
   let+ end_pos = get_pos in
   pure (Cst.Pi (Some { start_pos; end_pos }, group, b)))
    st

and parse_sigma_leading : Cst.t Parser.t =
 fun st ->
  (let* () = ws in
   let+ start_pos = get_pos in
   let* group = parse_typed_binder_group in
   let* () = times in
   let* b = pratt_parser PrecPi in
   let+ end_pos = get_pos in
   pure (Cst.Sigma (Some { start_pos; end_pos }, group, b)))
    st

and parse_unit : Cst.t Parser.t =
 fun st ->
  (let* () = ws in
   let+ start_pos = get_pos in
   let* () = str "(" in
   let* () = ws in
   let+ cp = get_cp in
   if cp = Some (Char.code ')') then
     let* () = advance_char in
     let+ end_pos = get_pos in
     pure (Cst.Ident (Some { start_pos; end_pos }, "Unit.unit"))
   else
     fail "expected unit")
    st

and parse_ann_pair_paren : Cst.t Parser.t =
 fun st ->
  (let* () = ws in
   let+ start_pos = get_pos in
   let* () = str "(" in
   let* e = parse_preterm in
   let* () = ws in
   let+ cp = get_cp in
   if cp = Some (Char.code ',') then
     let* () = str "," in
     let* b = parse_preterm in
     let* () = str ")" in
     let+ end_pos = get_pos in
     pure (Cst.Pair (Some { start_pos; end_pos }, e, b))
   else if cp = Some (Char.code ':') then
     let* () = str ":" in
     let* ty = parse_preterm in
     let* () = str ")" in
     let+ end_pos = get_pos in
     pure (Cst.Ann (Some { start_pos; end_pos }, e, ty))
   else
     let* () = str ")" in
     pure e)
    st

and parse_sorry : Cst.t Parser.t =
 fun st ->
  (let* () = ws in
   let+ start_pos = get_pos in
   let* () = keyword "sorry" in
   let+ end_pos = get_pos in
   pure (Cst.Sorry (Some { start_pos; end_pos })))
    st

and parse_type : Cst.t Parser.t =
 fun st ->
  (let* () = ws in
   let+ start_pos = get_pos in
   let* () = keyword "Type" in
   let+ end_pos = get_pos in
   pure (Cst.U (Some { start_pos; end_pos })))
    st

and parse_nat_lit : Cst.t Parser.t =
 fun st ->
  (let* () = ws in
   let+ start_pos = get_pos in
   let* n = parse_nat in
   let+ end_pos = get_pos in
   pure (Cst.NatLit (Some { start_pos; end_pos }, n)))
    st

and parse_ident_atom : Cst.t Parser.t =
 fun st ->
  (let* () = ws in
   let+ start_pos = get_pos in
   let* name = read_ident in
   let+ end_pos = get_pos in
   let kw =
     [
       "fun";
       "let";
       "def";
       "example";
       "axiom";
       "inductive";
       "structure";
       "where";
       "import";
     ]
   in
   if List.mem name kw then
     fail "keyword in expression"
   else
     pure (Cst.Ident (Some { start_pos; end_pos }, name)))
    st

and parse_atom_leading : Cst.t Parser.t =
 fun st ->
  (let+ eof = is_eof in
   if eof then
     fail "unexpected end of input"
   else
     choice
       [
         parse_unit;
         parse_ann_pair_paren;
         parse_sorry;
         parse_type;
         parse_nat_lit;
         parse_ident_atom;
       ]
       (fail "expected atom"))
    st

and pratt_parser min_prec : Cst.t Parser.t =
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
      (PrecApp, PrecApp, parse_app_trailing);
      (PrecMulL, PrecMulR, parse_mul_trailing);
      (PrecAddL, PrecAddR, parse_add_trailing);
      (PrecEq, PrecEq, parse_eq_trailing);
      (PrecPi, PrecPi, parse_prod_trailing);
      (PrecPi, PrecPi, parse_arrow_trailing);
    ]
  in
  let* () = ws in
  let rec try_leading = function
    | [] -> fail "expected expression"
    | (p_prec, p) :: ps ->
        if compare_prec p_prec min_prec >= 0 then
          p <|> try_leading ps
        else
          try_leading ps
  in
  let* left = try_leading leading_parsers in
  let rec parse_trailing left =
    let rec try_trailing = function
      | [] -> pure left
      | (left_prec, right_prec, p) :: ps ->
          if compare_prec left_prec min_prec >= 0 then
            p right_prec left >>= parse_trailing <|> try_trailing ps
          else
            try_trailing ps
    in
    try_trailing trailing_parsers
  in
  parse_trailing left

and parse_preterm : Cst.t Parser.t = fun st -> (pratt_parser PrecMin) st

and parse_app_trailing (_right_prec : prec) (left : Cst.t) : Cst.t Parser.t =
  (let* arg = parse_lambda_leading in
   let+ end_pos = get_pos in
   let start_pos = get_start_pos left in
   pure (Cst.App (Some { start_pos; end_pos }, left, arg)))
  <|> (let* arg = parse_let_leading in
       let+ end_pos = get_pos in
       let start_pos = get_start_pos left in
       pure (Cst.App (Some { start_pos; end_pos }, left, arg)))
  <|> let* arg = parse_atom_leading in
      let+ end_pos = get_pos in
      let start_pos = get_start_pos left in
      pure (Cst.App (Some { start_pos; end_pos }, left, arg))

and parse_mul_trailing (right_prec : prec) (left : Cst.t) : Cst.t Parser.t =
  let* () = ws in
  let+ cp = get_cp in
  match cp with
  | Some cp when cp = Char.code '*' ->
      let* () = advance_char in
      let* b = pratt_parser right_prec in
      let+ end_pos = get_pos in
      let start_pos = get_start_pos left in
      pure (Cst.Mul (Some { start_pos; end_pos }, left, b))
  | _ -> fail "expected *"

and parse_add_trailing (right_prec : prec) (left : Cst.t) : Cst.t Parser.t =
  let* () = ws in
  let+ cp = get_cp in
  match cp with
  | Some cp when cp = Char.code '+' || cp = Char.code '-' ->
      let is_plus = cp = Char.code '+' in
      let* () = advance_char in
      let* b = pratt_parser right_prec in
      let+ end_pos = get_pos in
      let start_pos = get_start_pos left in
      if is_plus then
        pure (Cst.Add (Some { start_pos; end_pos }, left, b))
      else
        pure (Cst.Sub (Some { start_pos; end_pos }, left, b))
  | _ -> fail "expected + or -"

and parse_eq_trailing (right_prec : prec) (left : Cst.t) : Cst.t Parser.t =
  let* () = ws in
  let+ cp = get_cp in
  match cp with
  | Some cp when cp = Char.code '=' ->
      let* () = advance_char in
      let* b = pratt_parser right_prec in
      let+ end_pos = get_pos in
      let start_pos = get_start_pos left in
      pure (Cst.Eq (Some { start_pos; end_pos }, left, b))
  | _ -> fail "expected ="

and parse_prod_trailing (right_prec : prec) (left : Cst.t) : Cst.t Parser.t =
  let* () = times in
  let* b = pratt_parser right_prec in
  let+ end_pos = get_pos in
  let start_pos = get_start_pos left in
  pure (Cst.Prod (Some { start_pos; end_pos }, left, b))

and parse_arrow_trailing (right_prec : prec) (left : Cst.t) : Cst.t Parser.t =
  let* () = arrow in
  let* b = pratt_parser right_prec in
  let+ end_pos = get_pos in
  let start_pos = get_start_pos left in
  pure (Cst.Arrow (Some { start_pos; end_pos }, left, b))

(* ========== Top level items ========== *)

let parse_params : Cst.typed_binder_group list Parser.t =
  many parse_typed_binder_group

let parse_constructor : Cst.Command.inductive_constructor Parser.t =
  let* () = ws in
  let+ start_pos = get_pos in
  let* () = str "|" in
  let* _info, name = parse_ident in
  let* params = parse_params in
  let* ty_opt = optional (str ":" >> parse_preterm) in
  let+ end_pos = get_pos in
  pure { Cst.Command.src = Some { start_pos; end_pos }; name; params; ty_opt }

let parse_inductive : Cst.Command.t Parser.t =
  let+ start_pos = get_pos in
  let* () = keyword "inductive" in
  let* _info, name = parse_ident in
  let* params = parse_params in
  let* ty_opt = optional (str ":" >> parse_preterm) in
  let* () = keyword "where" in
  let* ctors = many parse_constructor in
  let+ end_pos = get_pos in
  pure
    (Cst.Command.Inductive
       { src = Some { start_pos; end_pos }; name; params; ty_opt; ctors })

let parse_field : Cst.Command.structure_field Parser.t =
  let+ start_pos = get_pos in
  let* () = str "(" in
  let* _src, name = parse_ident in
  if String.contains name '.' then
    fail "Structure field names must be atomic"
  else
    let* args = parse_params in
    let* () = str ":" in
    let* ty = parse_preterm in
    let* () = str ")" in
    let+ end_pos = get_pos in
    pure
      { Cst.Command.src = Some { start_pos; end_pos }; name; params = args; ty }

let parse_structure : Cst.Command.t Parser.t =
  let+ start_pos = get_pos in
  let* () = keyword "structure" in
  let* _info, name = parse_ident in
  let* params = parse_params in
  let* ty_opt =
    optional
      (let* () = str ":" in
       parse_preterm)
  in
  let* () = keyword "where" in
  let* fields = many parse_field in
  let+ end_pos = get_pos in
  pure
    (Cst.Command.Structure
       { src = Some { start_pos; end_pos }; name; params; ty_opt; fields })

let parse_def_body :
    (Cst.typed_binder_group list * Cst.t option * Cst.t) Parser.t =
  let* params = parse_params in
  let* ret_ty_opt =
    optional
      (let* () = str ":" in
       parse_preterm)
  in
  let* () = keyword ":=" in
  let* body = parse_preterm in
  pure (params, ret_ty_opt, body)

let parse_def : Cst.Command.t Parser.t =
  let+ start_pos = get_pos in
  let* () = keyword "def" in
  let* _src, name = parse_ident in
  let* params, ty_opt, body = parse_def_body in
  let+ end_pos = get_pos in
  pure
    (Cst.Command.Definition
       { src = Some { start_pos; end_pos }; name; params; ty_opt; body })

let parse_example : Cst.Command.t Parser.t =
  let+ start_pos = get_pos in
  let* () = keyword "example" in
  let* params, ty_opt, body = parse_def_body in
  let+ end_pos = get_pos in
  pure
    (Cst.Command.Example
       { src = Some { start_pos; end_pos }; params; ty_opt; body })

let parse_axiom : Cst.Command.t Parser.t =
  let+ start_pos = get_pos in
  let* () = keyword "axiom" in
  let* _src, name = parse_ident in
  let* params = parse_params in
  let* () = str ":" in
  let* ty = parse_preterm in
  let+ end_pos = get_pos in
  pure
    (Cst.Command.Axiom { src = Some { start_pos; end_pos }; name; params; ty })

let parse_import : Cst.Command.t Parser.t =
  let+ start_pos = get_pos in
  let* () = keyword "import" in
  let* _info, module_name = parse_ident in
  let+ end_pos = get_pos in
  pure (Cst.Command.Import { src = Some { start_pos; end_pos }; module_name })

let parse_item : Cst.Command.t Parser.t =
  choice
    [
      parse_import;
      parse_def;
      parse_example;
      parse_axiom;
      parse_inductive;
      parse_structure;
    ]
    (fail "unexpected end of input")

let rec parse_program acc : Cst.program Parser.t =
  let* () = ws in
  let+ eof = is_eof in
  if eof then
    pure (List.rev acc)
  else
    let* item = parse_item in
    parse_program (item :: acc)

let parse s =
  match parse_program [] (init_state s) with
  | Ok (prog, _) -> prog
  | Error e -> raise (Syntax_error e)
