type t = string list

let compare = List.compare String.compare
let equal = List.equal String.equal
let to_string = String.concat "."
let pp fmt name = Format.fprintf fmt "%s" (to_string name)
let child parent name = parent @ [ name ]
let parse = String.split_on_char '.'
