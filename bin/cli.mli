type options = {
  input_file : string;
  show_parse : bool;
  show_elab : string list;
  watch : bool;
}

val parse_args : unit -> options
