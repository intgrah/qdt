type options = {
  input_file : string;
  show_lex : bool;
  show_parse : bool;
  show_elab : bool;
}

val parse_args : unit -> options
