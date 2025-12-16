type t

val compare : t -> t -> int
val equal : t -> t -> bool
val to_string : t -> string
val parse : string -> t
val to_path : string -> t -> string
