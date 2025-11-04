type options = {
  input_file : string;
  show_tokens : bool;
  show_parse : bool;
  show_elaboration : bool;
}

val parse_args : unit -> options
