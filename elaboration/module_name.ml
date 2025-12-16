type t = string list

let compare = List.compare String.compare
let equal = List.equal String.equal
let to_string = String.concat "."
let parse = String.split_on_char '.'
