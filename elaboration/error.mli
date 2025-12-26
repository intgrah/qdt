open Frontend.Syntax

type location = { span : span }

type t = {
  message : string;
  location : location option; (* None = synthetic/untraceable source *)
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

val make : ?location:location option -> kind:kind -> string -> t
val make_with_src_t : kind:kind -> string -> Frontend.Syntax.src -> t
val make_with_src : kind:kind -> string -> Frontend.Syntax.src -> exn
val pp : filename:string -> Format.formatter -> t -> unit
val to_string : filename:string -> t -> string
