exception Parse_error of string
exception Tokens_remaining of Lexer.token list

val parse : Lexer.token list -> Elaboration.Syntax.Raw.program
