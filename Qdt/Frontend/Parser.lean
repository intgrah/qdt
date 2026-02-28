import Lean
import Qdt.Frontend.Cst

namespace Qdt.Frontend.Parser

open Lean (Name SyntaxNodeKind)
open Cst

structure ParseError where
  msg : String
  pos : Nat
deriving Repr, Inhabited

private structure State where
  input : String
  pos : Nat
deriving Inhabited

private abbrev ParserM := StateT State (Except ParseError)

private def getPos : ParserM Nat := return (← get).pos
private def setPos (pos : Nat) : ParserM Unit := modify fun st => { st with pos }
private def isEof : ParserM Bool := do let st ← get; return st.pos ≥ st.input.utf8ByteSize
private def fail {α} (msg : String) : ParserM α := do throw ⟨msg, ← getPos⟩

private def peekChar? : ParserM (Option Char) := do
  let st ← get
  if st.pos ≥ st.input.utf8ByteSize then return none
  else return some (String.Pos.Raw.get st.input ⟨st.pos⟩)

private def peekString (n : Nat) : ParserM String := do
  let st ← get
  let endPos := min (st.pos + n) st.input.utf8ByteSize
  return String.Pos.Raw.extract st.input ⟨st.pos⟩ ⟨endPos⟩

private def advanceChar : ParserM Unit := do
  let st ← get
  if st.pos ≥ st.input.utf8ByteSize then fail "unexpected end of input"
  else
    let c := String.Pos.Raw.get st.input ⟨st.pos⟩
    set { st with pos := st.pos + c.utf8Size }

private partial def ws : ParserM Cst := do
  let some c ← peekChar? | fail "expected whitespace"
  if !c.isWhitespace then fail "expected whitespace"
  go ""
where
  go (acc : String) : ParserM Cst := do
    match ← peekChar? with
    | some c => if c.isWhitespace then advanceChar; go (acc.push c) else return .token `ws acc
    | none => return .token `ws acc

private def lineComment : ParserM Cst := do
  let mut acc := "--"
  advanceChar; advanceChar
  while true do
    match ← peekChar? with
    | some '\n' => acc := acc.push '\n'; advanceChar; break
    | some c => acc := acc.push c; advanceChar
    | none => break
  return .token `comment acc

private partial def blockComment : ParserM Cst := do
  advanceChar; advanceChar
  go "/-" 1
where
  go (acc : String) (depth : Nat) : ParserM Cst := do
    if ← isEof then fail "unterminated block comment"
    match ← peekString 2 with
    | "/-" => advanceChar; advanceChar; go (acc ++ "/-") (depth + 1)
    | "-/" => advanceChar; advanceChar; if depth == 1 then return .token `comment (acc ++ "-/") else go (acc ++ "-/") (depth - 1)
    | _ =>
        match ← peekChar? with
        | some c => advanceChar; go (acc.push c) depth
        | none => fail "unterminated block comment"

private partial def trivia : ParserM (Array Cst) := do
  let mut arr : Array Cst := #[]
  while true do
    match ← peekChar? with
    | some c =>
        if c.isWhitespace then arr := arr.push (← ws)
        else if c == '-' then
          match ← peekString 2 with
          | "--" => arr := arr.push (← lineComment)
          | _ => break
        else if c == '/' then
          match ← peekString 2 with
          | "/-" => arr := arr.push (← blockComment)
          | _ => break
        else break
    | none => break
  return arr


private def atomRaw (s : String) : ParserM Cst := do
  for c in s.toList do
    match ← peekChar? with
    | some c' => if c == c' then advanceChar else fail s!"expected '{s}'"
    | none => fail s!"expected '{s}'"
  return .token `atom s

private def isIdentStart (c : Char) : Bool := c.isAlpha || c == '_' || c == '\''
private def isIdentChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '\'' || c == '.'

private partial def readIdentChars : ParserM String := do
  let some c ← peekChar? | fail "expected identifier"
  if !isIdentStart c then fail "expected identifier"
  let mut acc := ""
  acc := acc.push c
  advanceChar
  while true do
    match ← peekChar? with
    | some '.' =>
        let pos ← getPos
        advanceChar
        match ← peekChar? with
        | some '{' => setPos pos; break
        | some c' =>
            if isIdentStart c' then acc := acc.push '.'
            else setPos pos; break
        | none => setPos pos; break
    | some c' =>
        if isIdentChar c' then acc := acc.push c'; advanceChar
        else break
    | none => break
  return acc

private def keywords : List String := ["fun", "let", "def", "example", "axiom", "inductive", "structure", "where", "import", "sorry", "Type"]

private def identRaw : ParserM Cst := do
  let name ← readIdentChars
  if name ∈ keywords then fail "keyword in identifier position"
  return .token `ident name

private def numRaw : ParserM Cst := do
  let some c ← peekChar? | fail "expected number"
  if !c.isDigit then fail "expected number"
  let mut s := ""
  while true do
    match ← peekChar? with
    | some d =>
        if d.isDigit then s := s.push d; advanceChar
        else break
    | none => break
  return .token `num s

private def tryParse {α} (p : ParserM α) : ParserM (Option α) := do
  let pos ← getPos
  (do let a ← p; return some a) <|> (do setPos pos; return none)

instance {α} : OrElse (ParserM α) where
  orElse p q := do
    match ← tryParse p with
    | some a => return a
    | none => q ()

private def peekIdentStr : ParserM (Option String) := do
  let pos ← getPos
  match ← peekChar? with
  | some c =>
      if isIdentStart c then
        let name ← readIdentChars
        setPos pos
        return some name
      else return none
  | none => return none

private def one (p : ParserM Cst) : ParserM (Array Cst) := do return #[← p]

private def opt (p : ParserM Cst) : ParserM (Array Cst) := do
  match ← tryParse p with
  | some c => return #[c]
  | none => return #[]

instance : Append (ParserM (Array Cst)) where
  append p q := return (← p) ++ (← q)

private def node (kind : SyntaxNodeKind) (p : ParserM (Array Cst)) : ParserM Cst := do
  return Cst.node kind (← p)

private partial def many (p : ParserM (Array Cst)) : ParserM (Array Cst) := do
  match ← tryParse p with
  | some cs => return cs ++ (← many p)
  | none => return #[]

private def wsSep1 (p : ParserM Cst) : ParserM (Array Cst) := do
  one p ++ many (trivia ++ one p)

private def commaSep1 (p : ParserM Cst) : ParserM (Array Cst) := do
  one p ++ many (trivia ++ one (atomRaw ",") ++ trivia ++ one p)

mutual

partial def levelAtom : ParserM Cst := do
  match ← peekChar? with
  | some '(' =>
      node `Lean.Parser.Level.paren <| one (atomRaw "(") ++ trivia ++ one level ++ trivia ++ one (atomRaw ")")
  | some ch =>
      if ch.isDigit then
        node `Lean.Parser.Level.num <| one numRaw
      else
        match ← peekIdentStr with
        | some "max" => node `Lean.Parser.Level.max <| one (atomRaw "max") ++ one ws ++ wsSep1 levelAtom
        | some name =>
            if name ∈ keywords then fail "expected level"
            node `Lean.Parser.Level.ident <| one identRaw
        | none => fail "expected level"
  | none => fail "expected level"

partial def level : ParserM Cst := do
  let base ← levelAtom
  (do let rest ← trivia ++ one (atomRaw "+") ++ trivia ++ one numRaw
      return Cst.node `Lean.Parser.Level.addLit (#[base] ++ rest))
  <|> pure base

partial def univParams : ParserM Cst :=
  node `Lean.Parser.Command.univParams (one (atomRaw ".") ++ one (atomRaw "{") ++ trivia ++ commaSep1 identRaw ++ trivia ++ one (atomRaw "}"))
  <|> pure (Cst.node `null #[])

partial def univArgs : ParserM Cst :=
  node `Lean.Parser.Term.univArgs (one (atomRaw ".") ++ one (atomRaw "{") ++ trivia ++ commaSep1 level ++ trivia ++ one (atomRaw "}"))
  <|> pure (Cst.node `null #[])

partial def hole : ParserM Cst :=
  node `Lean.Parser.Term.hole <| one (atomRaw "_")

partial def explicitBinder : ParserM Cst :=
  node ``Lean.Parser.Term.explicitBinder <|
    one (atomRaw "(") ++ trivia ++ wsSep1 binderName ++ trivia ++
    one (atomRaw ":") ++ trivia ++ one term ++ trivia ++ one (atomRaw ")")

partial def binderName : ParserM Cst := do
  let s ← peekString 2
  match s.toList with
  | '_' :: c :: _ => if isIdentChar c then identRaw else hole
  | '_' :: [] => hole
  | _ => identRaw

partial def term : ParserM Cst := pratt 0

partial def pratt (minPrec : Nat) : ParserM Cst := do
  let mut left ← leading minPrec
  while true do
    let pos ← getPos
    match ← trailing minPrec left with
    | some t => left := t
    | none => setPos pos; break
  return left

partial def leading (_minPrec : Nat) : ParserM Cst := do
  if ← isEof then fail "expected expression"
  match ← peekIdentStr with
  | some "fun" => parseLam
  | some "let" => parseLet
  | some "sorry" => parseSorry
  | some "Type" => parseType
  | _ =>
      match ← peekChar? with
      | some '(' => parseUnit <|> parseParenOrPi
      | some c =>
          if c.isDigit then
            let n ← numRaw
            return Cst.node `Lean.Parser.Term.num #[n]
          else
            parseIdentWithUniv
      | none => fail "expected expression"

partial def trailing (minPrec : Nat) (left : Cst) : ParserM (Option Cst) := do
  let triviaArr ← trivia
  let binop (kind : SyntaxNodeKind) (prec : Nat) (op : ParserM Cst) : ParserM (Option Cst) := do
    if minPrec > prec then return none
    let opToken ← op
    let rhs ← trivia ++ one (pratt (prec + 1))
    return some (Cst.node kind (#[left] ++ triviaArr ++ #[opToken] ++ rhs))
  match ← peekChar? with
  | some '-' =>
      match ← tryParse (atomRaw "->" <|> atomRaw "→") with
      | some arr =>
          if minPrec > 25 then return none
          let rhs ← trivia ++ one (pratt 25)
          return some (Cst.node `Lean.Parser.Term.arrow (#[left] ++ triviaArr ++ #[arr] ++ rhs))
      | none =>
          if triviaArr.isEmpty then return none
          tryAppArg minPrec left triviaArr
  | some '→' =>
      if minPrec > 25 then return none
      let arr ← atomRaw "→"
      let rhs ← trivia ++ one (pratt 25)
      return some (Cst.node `Lean.Parser.Term.arrow (#[left] ++ triviaArr ++ #[arr] ++ rhs))
  | some '=' => binop `«term_=_» 50 (atomRaw "=")
  | some '+' => binop `«term_+_» 65 (atomRaw "+")
  | _ =>
      if triviaArr.isEmpty then return none
      tryAppArg minPrec left triviaArr

partial def tryAppArg (minPrec : Nat) (left : Cst) (triviaArr : Array Cst) : ParserM (Option Cst) := do
  if minPrec > 1024 then return none
  match ← tryParse atomArg with
  | some arg => return some (Cst.node `Lean.Parser.Term.app (#[left] ++ triviaArr ++ #[arg]))
  | none => return none

partial def atomArg : ParserM Cst := do
  match ← peekIdentStr with
  | some "sorry" => parseSorry
  | some "Type" => parseType
  | some name =>
      if name ∈ keywords then fail "keyword"
      parseIdentWithUniv
  | none =>
      match ← peekChar? with
      | some '(' => parseUnit <|> parseParen
      | some c => if c.isDigit then return Cst.node `Lean.Parser.Term.num #[← numRaw] else fail "expected argument"
      | none => fail "expected argument"

partial def parseIdentWithUniv : ParserM Cst := do
  let i ← identRaw
  let univs ← univArgs
  match univs with
  | .node `null #[] => return Cst.node `Lean.Parser.Term.ident #[i]
  | _ => return Cst.node `Lean.Parser.Term.explicitUniv #[i, univs]

partial def parseLam : ParserM Cst :=
  node `Lean.Parser.Term.fun <|
    one (atomRaw "fun") ++ one ws ++ wsSep1 parseFunBinder ++ trivia ++
    one (atomRaw "=>" <|> atomRaw "⇒") ++ trivia ++ one term

partial def parseFunBinder : ParserM Cst := do
  match ← peekChar? with
  | some '(' => explicitBinder
  | _ => binderName

partial def optTypeAnnot : ParserM (Array Cst) := do
  let s ← peekString 2
  if s == ":=" then return #[]
  match ← peekChar? with
  | some ':' => one (atomRaw ":") ++ trivia ++ one term ++ trivia
  | _ => return #[]

partial def parseLet : ParserM Cst :=
  node `Lean.Parser.Term.let <|
    one (atomRaw "let") ++ one ws ++ one identRaw ++ trivia ++ optTypeAnnot ++
    one (atomRaw ":=") ++ trivia ++ one term ++ trivia ++ one (atomRaw ";") ++ trivia ++ one term

partial def parseSorry : ParserM Cst :=
  node `Lean.Parser.Term.sorry <| one (atomRaw "sorry")

partial def optLevel : ParserM (Array Cst) :=
  (one ws ++ one level) <|> pure #[]

partial def parseType : ParserM Cst :=
  node `Lean.Parser.Term.type <| one (atomRaw "Type") ++ optLevel

partial def parseUnit : ParserM Cst :=
  node `Lean.Parser.Term.unit <| one (atomRaw "(") ++ trivia ++ one (atomRaw ")")

partial def parseParen : ParserM Cst := do
  let pre ← one (atomRaw "(") ++ trivia ++ one term ++ trivia
  match ← peekChar? with
  | some ':' =>
      node `Lean.Parser.Term.typeAscription <|
        pure pre ++ one (atomRaw ":") ++ trivia ++ one term ++ trivia ++ one (atomRaw ")")
  | _ =>
      node `Lean.Parser.Term.paren <| pure pre ++ one (atomRaw ")")

partial def parseDepArrow : ParserM Cst :=
  node `Lean.Parser.Term.depArrow <|
    one explicitBinder ++ trivia ++ one (atomRaw "->" <|> atomRaw "→") ++ trivia ++ one (pratt 25)

partial def parseParenOrPi : ParserM Cst :=
  parseDepArrow <|> parseParen

partial def declId : ParserM Cst := do
  let ident ← identRaw
  let univs ← univParams
  let univArr := match univs with
    | .node `null #[] => #[]
    | _ => #[univs]
  return Cst.node `Lean.Parser.Command.declId (#[ident] ++ univArr)

partial def typeSig : ParserM (Array Cst) := do
  let s ← peekString 2
  if s == ":=" then fail "not a type sig"
  one ws ++ one (atomRaw ":") ++ trivia ++ one term

partial def optTypeSig : ParserM (Array Cst) :=
  typeSig <|> pure #[]

partial def optDeclSig : ParserM Cst :=
  node `Lean.Parser.Command.optDeclSig <| many (trivia ++ one explicitBinder) ++ optTypeSig

partial def declSig : ParserM Cst :=
  node `Lean.Parser.Command.declSig <|
    many (trivia ++ one explicitBinder) ++ trivia ++ one (atomRaw ":") ++ trivia ++ one term

partial def declValSimple : ParserM Cst :=
  node `Lean.Parser.Command.declValSimple <| one (atomRaw ":=") ++ trivia ++ one term

partial def parseDefinition : ParserM Cst :=
  node `Lean.Parser.Command.definition <|
    one (atomRaw "def") ++ one ws ++ one declId ++ one optDeclSig ++ trivia ++ one declValSimple

partial def parseExample : ParserM Cst :=
  node `Lean.Parser.Command.example <| one (atomRaw "example") ++ one optDeclSig ++ trivia ++ one declValSimple

partial def parseAxiom : ParserM Cst :=
  node `Lean.Parser.Command.axiom <| one (atomRaw "axiom") ++ one ws ++ one declId ++ one declSig

partial def parseCtor : ParserM Cst :=
  node `Lean.Parser.Command.ctor <| one (atomRaw "|") ++ trivia ++ one identRaw ++ one optDeclSig

partial def parseInductive : ParserM Cst :=
  node `Lean.Parser.Command.inductive <|
    one (atomRaw "inductive") ++ one ws ++ one declId ++ one optDeclSig ++ trivia ++
    opt (atomRaw "where") ++ trivia ++ opt parseCtor ++ many (trivia ++ one parseCtor)

partial def parseStructField : ParserM Cst :=
  node `Lean.Parser.Command.structField <|
    one (atomRaw "(") ++ trivia ++ one identRaw ++ one optDeclSig ++ trivia ++ one (atomRaw ")")

partial def parseStructure : ParserM Cst :=
  node `Lean.Parser.Command.structure <|
    one (atomRaw "structure") ++ one ws ++ one declId ++ one optDeclSig ++ trivia ++
    one (atomRaw "where") ++ trivia ++ one parseStructField ++ many (trivia ++ one parseStructField)

partial def parseImport : ParserM Cst :=
  node `Lean.Parser.Command.import <| one (atomRaw "import") ++ one ws ++ one identRaw

partial def parseCommand : ParserM Cst := do
  match ← peekIdentStr with
  | some "def" => parseDefinition
  | some "example" => parseExample
  | some "axiom" => parseAxiom
  | some "inductive" => parseInductive
  | some "structure" => parseStructure
  | some "import" => parseImport
  | _ => fail "expected command"

partial def parseProgram : ParserM Cst :=
  node `Lean.Parser.Module <|
    trivia ++ many (one parseImport ++ trivia) ++ many (one parseCommand ++ trivia)

end

def parse (input : String) : Except ParseError Cst :=
  match parseProgram.run { input, pos := 0 } with
  | .ok (cst, _) => .ok cst
  | .error e => .error e

def parseExpr (input : String) : Except ParseError Cst :=
  match term.run { input, pos := 0 } with
  | .ok (cst, _) => .ok cst
  | .error e => .error e

partial def showTree (cst : Cst) (indent : Nat := 0) : String :=
  let pfx := "".pushn ' ' (indent * 2)
  match cst with
  | .token kind val =>
      let k := toString kind
      pfx ++ k ++ "@" ++ toString val.length ++ " \"" ++ val ++ "\"\n"
  | .node kind args =>
      let k := toString kind
      let hdr := pfx ++ k ++ "@" ++ toString cst.width ++ "\n"
      let children := args.map (fun child => showTree child (indent + 1))
      hdr ++ String.join children.toList

end Qdt.Frontend.Parser
