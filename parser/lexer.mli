exception Unterminated_comment
exception Illegal_character

val scan : Token.t list -> char list -> Token.t list
