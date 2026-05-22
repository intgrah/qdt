; Comments
(line_comment) @comment
(block_comment) @comment

; Numbers
(number) @number

; Default identifier; more-specific captures below override.
(identifier) @variable

; Hole
"_" @variable.builtin

; Operators
"->" @operator
"→"  @operator
"=>" @operator
"⇒"  @operator
":=" @operator
"="  @operator
"+"  @operator

; Punctuation
":" @punctuation.delimiter
";" @punctuation.delimiter
"," @punctuation.delimiter
"|" @punctuation.delimiter

; Brackets
"(" @punctuation.bracket
")" @punctuation.bracket
"{" @punctuation.bracket
"}" @punctuation.bracket

; Term keywords
"fun"   @keyword.function
"let"   @keyword
"max"   @keyword
"sorry" @keyword.exception

; Builtin type
"Type" @type.builtin

; Declaration keywords
"def"       @keyword
"example"   @keyword
"axiom"     @keyword
"inductive" @keyword
"structure" @keyword
"import"    @keyword.import
"where"     @keyword

; Universe parameters
(univ_param) @type.parameter

; Declaration heads
(import      name: (identifier) @namespace)
(definition  name: (identifier) @function)
(axiom       name: (identifier) @function)
(inductive   name: (identifier) @type)
(structure   name: (identifier) @type)

; Constructor names
(ctor name: (identifier) @constructor)
