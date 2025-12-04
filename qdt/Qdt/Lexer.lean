import Parser

namespace Qdt

open Parser

inductive Token where
  | lparen
  | rparen
  | colon
  | arrow
  | eqGt
  | comma
  | colonEq
  | semicolon
  | times
  | plus
  | minus
  | equal
  | «def»
  | «let»
  | fun
  | fst
  | snd
  | refl
  | absurd
  | sorry
  | type
  | unit
  | empty
  | int
  | underscore
  | ident : String → Token
  | intLit : Int → Token
  deriving Repr, Inhabited, BEq

def Token.toString : Token → String
  | .lparen => "("
  | .rparen => ")"
  | .colon => ":"
  | .arrow => "→"
  | .eqGt => "=>"
  | .comma => ","
  | .colonEq => ":="
  | .semicolon => ";"
  | .times => "×"
  | .plus => "+"
  | .minus => "-"
  | .equal => "="
  | .def => "def"
  | .let => "let"
  | .fun => "fun"
  | .fst => "fst"
  | .snd => "snd"
  | .refl => "refl"
  | .absurd => "absurd"
  | .sorry => "sorry"
  | .type => "Type"
  | .unit => "Unit"
  | .empty => "Empty"
  | .int => "Int"
  | .underscore => "_"
  | .ident s => s
  | .intLit n => s!"{n}"

instance : ToString Token := ⟨Token.toString⟩

def isAlphaNum (c : Char) : Bool :=
  c.isAlphanum || c == '_'

abbrev LexerM := SimpleParser Substring.Raw Char

def pWhitespace1 : LexerM Unit :=
  dropMany1 (tokenFilter Char.isWhitespace)

def pLineComment : LexerM Unit := do
  let _ ← Char.chars "--"
  dropMany (tokenFilter (· != '\n'))

partial def pBlockComment : LexerM Unit := do
  let _ ← Char.chars "/-"
  let rec go (depth : Nat) : LexerM Unit := do
    if depth == 0 then
      return ()
    else
      (do let _ ← Char.chars "/-"; go (depth + 1))
      <|> (do let _ ← Char.chars "-/"; go (depth - 1))
      <|> (do let _ ← anyToken; go depth)
  go 1

def pSkip : LexerM Unit :=
  dropMany (pWhitespace1 <|> pLineComment <|> pBlockComment)

def pIdent : LexerM String := do
  let c ← tokenFilter (fun c => c.isAlpha || c == '_')
  let cs ← foldl String.push "" (tokenFilter isAlphaNum)
  return c.toString ++ cs

def pNat : LexerM Nat := do
  let digits ← takeMany1 (tokenFilter Char.isDigit)
  return digits.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

def pInt : LexerM Int := do
  let neg ← option? (token '-')
  let n ← pNat
  return if neg.isSome then -(n : Int) else (n : Int)

def pToken : LexerM Token :=
  (Char.chars "=>" *> pure Token.eqGt)
  <|> (Char.chars ":=" *> pure Token.colonEq)
  <|> (Char.chars "->" *> pure Token.arrow)
  <|> (Char.chars "→" *> pure Token.arrow)
  <|> (Char.chars "×" *> pure Token.times)
  <|> (token '(' *> pure Token.lparen)
  <|> (token ')' *> pure Token.rparen)
  <|> (token ':' *> pure Token.colon)
  <|> (token ',' *> pure Token.comma)
  <|> (token ';' *> pure Token.semicolon)
  <|> (token '*' *> pure Token.times)
  <|> (token '+' *> pure Token.plus)
  <|> (token '-' *> pure Token.minus)
  <|> (token '=' *> pure Token.equal)
  <|> (do
      let s ← pIdent
      return match s with
        | "_" => Token.underscore
        | "def" => Token.def
        | "let" => Token.let
        | "fun" => Token.fun
        | "Type" => Token.type
        | "Unit" => Token.unit
        | "Empty" => Token.empty
        | "Int" => Token.int
        | "fst" => Token.fst
        | "snd" => Token.snd
        | "refl" => Token.refl
        | "absurd" => Token.absurd
        | "sorry" => Token.sorry
        | _ => Token.ident s)
  <|> (Token.intLit <$> pInt)

def pTokens : LexerM (Array Token) := do
  pSkip
  let tokens ← takeMany (pToken <* pSkip)
  endOfInput
  return tokens

def tokenize (s : String) : Except String (List Token) :=
  match Parser.run pTokens s.toSubstring with
  | .ok _ tokens => .ok tokens.toList
  | .error _ msg => .error (repr msg).pretty

end Qdt
