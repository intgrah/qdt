type t

val compare : t -> t -> int
val equal : t -> t -> bool
val to_string : t -> string
val pp : Format.formatter -> t -> unit
val child : t -> string -> t
val parse : string -> t
