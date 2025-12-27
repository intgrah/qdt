type options = {
  input_file : string;
  root_dir : string;
  show_parse : bool;
  show_elab : string list;
  watch : bool;
}

val parse_args : unit -> options
