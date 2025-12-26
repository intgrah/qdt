open Frontend

type location = { span : Syntax.span }

type t = {
  message : string;
  location : location option;
  kind : kind;
}

and kind =
  | Parse
  | Elaboration
  | Type_check
  | Positivity
  | Import
  | Eval

exception Error of t

let make ?(location = None) ~kind message = { message; location; kind }

let make_with_src_t ~kind message (src : Syntax.src) : t =
  let location =
    match src with
    | None -> None
    | Some { start_pos; end_pos } -> Some { span = { start_pos; end_pos } }
  in
  { message; location; kind }

let make_with_src ~kind message (src : Syntax.src) : exn =
  Error (make_with_src_t ~kind message src)

let pp ~filename fmt err =
  match err.location with
  | Some { span } ->
      Format.fprintf fmt "%s:%d:%d: %s" filename span.start_pos.line
        span.start_pos.column err.message
  | None -> Format.fprintf fmt "%s" err.message

let to_string ~filename = Format.asprintf "%a" (pp ~filename)
