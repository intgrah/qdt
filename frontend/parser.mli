exception Syntax_error of string

val parse : Lexer.token list -> Raw_syntax.program
