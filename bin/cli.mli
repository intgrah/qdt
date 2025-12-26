type options = {
  input_file : string;
  root_dir : string;
  show_parse : bool;
  show_elab : bool;
  watch : bool;
}

val parse_args : unit -> options
