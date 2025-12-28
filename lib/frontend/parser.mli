type parse_error = {
  msg : string;
  pos : Source.position;
}

exception Syntax_error of parse_error

type prec =
  | PrecMin
  | PrecLet
  | PrecFun
  | PrecPi
  | PrecEq
  | PrecAddL
  | PrecAddR
  | PrecMulL
  | PrecMulR
  | PrecApp
  | PrecMax

val compare_prec : prec -> prec -> int
val parse : string -> Cst.program
