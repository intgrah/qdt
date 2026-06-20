module

public import Qdt.Frontend.Cst
public import Lean.Data.Trie

@[expose] public section

namespace Qdt.Frontend.Parser

open Lean (Name SyntaxNodeKind)
open Cst

structure ParseError where
  msg : String
  pos : Nat
deriving Repr, Inhabited, Hashable

structure IdentCacheEntry where
  startPos : Nat
  stopPos  : Nat
  value    : String
deriving Inhabited

structure State where
  input    : String
  pos      : Nat
  stack    : Array Cst
  errors   : Array ParseError
  errorMsg : Option ParseError
  identCache : IdentCacheEntry
deriving Inhabited

abbrev ParserFn := State → State

namespace State

@[inline] def hasError (s : State) : Bool := s.errorMsg.isSome
@[noinline] def stackSize (s : State) : Nat := s.stack.size
@[inline] def isEof (s : State) : Bool := s.pos ≥ s.input.utf8ByteSize

@[inline] def pushSyntax (s : State) (c : Cst) : State :=
  { s with stack := s.stack.push c }

@[inline] def popSyntax (s : State) : State :=
  { s with stack := s.stack.pop }

@[inline] def shrinkStack (s : State) (iniSz : Nat) : State :=
  { s with stack := s.stack.shrink iniSz }

@[inline] def setError (s : State) (msg : String) : State :=
  { s with errorMsg := some ⟨msg, s.pos⟩ }

@[inline] def setErrorAt (s : State) (msg : String) (pos : Nat) : State :=
  { s with errorMsg := some ⟨msg, pos⟩ }

@[inline] def clearError (s : State) : State :=
  { s with errorMsg := none }

@[inline] def restore (s : State) (iniSz : Nat) (iniPos : Nat) : State :=
  { s with stack := s.stack.shrink iniSz, errorMsg := none, pos := iniPos }

@[inline] def setPos (s : State) (pos : Nat) : State :=
  { s with pos := pos }

@[inline] def peekChar? (s : State) : Option Char :=
  if s.pos ≥ s.input.utf8ByteSize then none
  else some (String.Pos.Raw.get s.input ⟨s.pos⟩)

@[inline] def peekString (s : State) (n : Nat) : String :=
  let endPos := min (s.pos + n) s.input.utf8ByteSize
  String.Pos.Raw.extract s.input ⟨s.pos⟩ ⟨endPos⟩

@[inline] def mkNode (s : State) (k : SyntaxNodeKind) (iniSz : Nat) : State :=
  if s.hasError && s.stack.size == iniSz then
    s.pushSyntax (.token `missing "")
  else
    let kids := s.stack.extract iniSz s.stack.size
    { s with stack := (s.stack.shrink iniSz).push (.node k kids) }

end State

@[inline] def andthenFn (p q : ParserFn) : ParserFn := fun s =>
  let s := p s
  if s.hasError then s else q s

/-- >> syntax -/
instance : AndThen ParserFn where
  andThen p q := andthenFn p (q ())

@[inline] def orelseFn (p q : ParserFn) : ParserFn := fun s =>
  let iniSz := s.stackSize
  let iniPos := s.pos
  let s' := p s
  if s'.hasError && s'.pos == iniPos then q (s'.restore iniSz iniPos) else s'

/-- <|> syntax -/
instance : OrElse ParserFn where
  orElse p q := orelseFn p (q ())

@[inline] def atomicFn (p : ParserFn) : ParserFn := fun s =>
  let iniPos := s.pos
  let s' := p s
  if s'.hasError then { s' with pos := iniPos } else s'

@[inline] def nodeFn (k : SyntaxNodeKind) (p : ParserFn) : ParserFn := fun s =>
  let iniSz := s.stackSize
  (p s).mkNode k iniSz

@[inline] def optionalFn (p : ParserFn) : ParserFn := fun s =>
  let iniSz := s.stackSize
  let iniPos := s.pos
  let s' := p s
  if s'.hasError && s'.pos == iniPos then s'.restore iniSz iniPos else s'

@[inline] def lookaheadFn (p : ParserFn) : ParserFn := fun s =>
  let iniSz := s.stackSize
  let iniPos := s.pos
  let s' := p s
  if s'.hasError then s' else s'.restore iniSz iniPos

@[inline] def advanceCharFn : ParserFn := fun s =>
  if s.pos ≥ s.input.utf8ByteSize then s.setError "unexpected end of input"
  else
    let c := String.Pos.Raw.get s.input ⟨s.pos⟩
    { s with pos := s.pos + c.utf8Size }

def wsAdvanceFn (s : State) : State :=
  match h : s.peekChar? with
  | some c =>
      if c.isWhitespace then
        have hpos : s.pos < s.input.utf8ByteSize := by
          unfold State.peekChar? at h
          split at h <;> simp_all
        have : (s.input.utf8ByteSize - (s.pos + c.utf8Size)) < (s.input.utf8ByteSize - s.pos) := by
          have := c.utf8Size_pos
          omega
        wsAdvanceFn { s with pos := s.pos + c.utf8Size }
      else s
  | none => s
termination_by s.input.utf8ByteSize - s.pos

def wsFn : ParserFn := fun s =>
  match s.peekChar? with
  | some c =>
      if c.isWhitespace then
        let startPos := s.pos
        let s := wsAdvanceFn s
        s.pushSyntax (.token `ws (String.Pos.Raw.extract s.input ⟨startPos⟩ ⟨s.pos⟩))
      else s.setError "expected whitespace"
  | none => s.setError "expected whitespace"

def lineCommentAdvanceFn (s : State) : State :=
  match h : s.peekChar? with
  | some '\n' => { s with pos := s.pos + 1 }
  | some c =>
      have hpos : s.pos < s.input.utf8ByteSize := by
        unfold State.peekChar? at h
        split at h <;> simp_all
      have : (s.input.utf8ByteSize - (s.pos + c.utf8Size)) < (s.input.utf8ByteSize - s.pos) := by
        have := c.utf8Size_pos
        omega
      lineCommentAdvanceFn { s with pos := s.pos + c.utf8Size }
  | none => s
termination_by s.input.utf8ByteSize - s.pos

def lineCommentFn : ParserFn := fun s =>
  let startPos := s.pos
  let s := lineCommentAdvanceFn { s with pos := s.pos + 2 }
  s.pushSyntax (.token `comment (String.Pos.Raw.extract s.input ⟨startPos⟩ ⟨s.pos⟩))

def blockCommentAdvanceFn (depth : Nat) (s : State) : State :=
  if hbound : s.pos ≥ s.input.utf8ByteSize then s.setError "unterminated block comment"
  else
    match h : s.peekString 2 with
    | "/-" =>
        have : (s.input.utf8ByteSize - (s.pos + 2)) < (s.input.utf8ByteSize - s.pos) := by
          omega
        blockCommentAdvanceFn (depth + 1) { s with pos := s.pos + 2 }
    | "-/" =>
        if depth == 1 then { s with pos := s.pos + 2 }
        else
          have : (s.input.utf8ByteSize - (s.pos + 2)) < (s.input.utf8ByteSize - s.pos) := by
            omega
          blockCommentAdvanceFn (depth - 1) { s with pos := s.pos + 2 }
    | _ =>
        match h2 : s.peekChar? with
        | some c =>
            have hpos : s.pos < s.input.utf8ByteSize := by
              unfold State.peekChar? at h2
              split at h2 <;> simp_all
            have : (s.input.utf8ByteSize - (s.pos + c.utf8Size)) < (s.input.utf8ByteSize - s.pos) := by
              have := c.utf8Size_pos
              omega
            blockCommentAdvanceFn depth { s with pos := s.pos + c.utf8Size }
        | none => s.setError "unterminated block comment"
termination_by s.input.utf8ByteSize - s.pos

def blockCommentFn : ParserFn := fun s =>
  let startPos := s.pos
  let s := blockCommentAdvanceFn 1 { s with pos := s.pos + 2 }
  if s.hasError then s
  else s.pushSyntax (.token `comment (String.Pos.Raw.extract s.input ⟨startPos⟩ ⟨s.pos⟩))

partial def triviaFn : ParserFn := fun s =>
  match s.peekChar? with
  | some c =>
      if c.isWhitespace then
        let s := wsFn s
        if s.hasError then s else triviaFn s
      else if c == '-' then
        match s.peekString 2 with
        | "--" =>
            let s := lineCommentFn s
            if s.hasError then s else triviaFn s
        | _ => s
      else if c == '/' then
        match s.peekString 2 with
        | "/-" =>
            let s := blockCommentFn s
            if s.hasError then s else triviaFn s
        | _ => s
      else s
  | none => s

def readIdentCharsAux (acc : String) (s : State) : String × State :=
  match h : s.peekChar? with
  | some '.' =>
      let pos := s.pos
      let s' := { s with pos := s.pos + 1 }
      have hpos : s.pos < s.input.utf8ByteSize := by
        unfold State.peekChar? at h
        split at h <;> simp_all
      match s'.peekChar? with
      | some c' =>
          if Lean.isIdFirst c' then
            have : (s'.input.utf8ByteSize - s'.pos) < (s.input.utf8ByteSize - s.pos) := by
              show s.input.utf8ByteSize - (s.pos + 1) < s.input.utf8ByteSize - s.pos
              omega
            readIdentCharsAux (acc.push '.') s'
          else (acc, { s with pos := pos })
      | none => (acc, { s with pos := pos })
  | some c' =>
      if Lean.isIdRest c' then
        have hpos : s.pos < s.input.utf8ByteSize := by
          unfold State.peekChar? at h
          split at h <;> simp_all
        have : (s.input.utf8ByteSize - (s.pos + c'.utf8Size)) < (s.input.utf8ByteSize - s.pos) := by
          have := c'.utf8Size_pos
          omega
        readIdentCharsAux (acc.push c') { s with pos := s.pos + c'.utf8Size }
      else (acc, s)
  | none => (acc, s)
termination_by s.input.utf8ByteSize - s.pos

def readIdentChars (s : State) : String × State :=
  match s.peekChar? with
  | some c =>
      if Lean.isIdFirst c then
        let acc := "".push c
        let s := { s with pos := s.pos + c.utf8Size }
        readIdentCharsAux acc s
      else ("", s)
  | none => ("", s)

def tokenList : List String :=
  [ "(", ")", "{", "}", ":", ":=", ".", ",", ";", "+", "=", "=>", "⇒", "→", "->", "|", "_", "@",
    "fun", "let", "def", "example", "axiom", "inductive", "structure", "where", "import",
    "sorry", "Type", "max" ]

def tokens : Lean.Data.Trie String :=
  tokenList.foldl (fun t s => t.insert s s) .empty

@[inline] def isReserved (s : String) : Bool :=
  (tokens.find? s).isSome

@[inline] def tokenizeIdentAt (s : State) : State :=
  if s.identCache.startPos == s.pos then s
  else
    let startPos := s.pos
    let (name, s') := readIdentChars s
    let stopPos := s'.pos
    { s' with
      pos := startPos,
      identCache := { startPos, stopPos, value := name } }

@[inline] def peekIdentStr (s : State) : Option String × State :=
  let s := tokenizeIdentAt s
  let v := s.identCache.value
  (if v.isEmpty then none else some v, s)

def identRawFn : ParserFn := fun s =>
  let s := tokenizeIdentAt s
  let entry := s.identCache
  let name := entry.value
  if name.isEmpty then s.setError "expected identifier"
  else if isReserved name then s.setError "keyword in identifier position"
  else
    { s with pos := entry.stopPos }.pushSyntax (.token `ident name)

def numAdvanceFn (s : State) : State :=
  match h : s.peekChar? with
  | some c =>
      if c.isDigit then
        have hpos : s.pos < s.input.utf8ByteSize := by
          unfold State.peekChar? at h
          split at h <;> simp_all
        have : (s.input.utf8ByteSize - (s.pos + 1)) < (s.input.utf8ByteSize - s.pos) := by
          omega
        numAdvanceFn { s with pos := s.pos + 1 }
      else s
  | none => s
termination_by s.input.utf8ByteSize - s.pos

def numRawFn : ParserFn := fun s =>
  match s.peekChar? with
  | some c =>
      if c.isDigit then
        let startPos := s.pos
        let s := numAdvanceFn s
        s.pushSyntax (.token `num (String.Pos.Raw.extract s.input ⟨startPos⟩ ⟨s.pos⟩))
      else s.setError "expected number"
  | none => s.setError "expected number"

inductive Tok where
  | atom (s : String)
  | ident (s : String)
  | num (s : String)
  | unknown
deriving Inhabited, BEq

def peekTok (s : State) : Tok :=
  match s.peekChar? with
  | none => .unknown
  | some c =>
      if c.isDigit then
        .num (String.Pos.Raw.extract s.input ⟨s.pos⟩ ⟨(numAdvanceFn s).pos⟩)
      else if Lean.isIdFirst c then
        let name := (tokenizeIdentAt s).identCache.value
        if isReserved name then .atom name else .ident name
      else
        match Lean.Data.Trie.matchPrefix s.input tokens ⟨s.pos⟩ with
        | some tk => .atom tk
        | none    => .unknown

def symbolFn (sym : String) : ParserFn := fun s =>
  match peekTok s with
  | .atom v =>
      if v == sym then
        { s with pos := s.pos + sym.utf8ByteSize }.pushSyntax (.token `atom sym)
      else s.setError s!"expected '{sym}'"
  | _ => s.setError s!"expected '{sym}'"

partial def manyFn (p : ParserFn) : ParserFn := fun s =>
  let iniPos := s.pos
  let iniSz := s.stackSize
  let s' := p s
  if s'.hasError then
    if s'.pos == iniPos then s'.restore iniSz iniPos else s'
  else if s'.pos == iniPos then
    s'.setError "many: parser did not consume"
  else manyFn p s'

partial def skipUntilRecoveryFn : ParserFn := fun s =>
  if s.pos ≥ s.input.utf8ByteSize then s
  else
    let (id?, s) := peekIdentStr s
    match id? with
    | some k =>
        if isReserved k then s
        else
          match s.peekChar? with
          | some c => skipUntilRecoveryFn { s with pos := s.pos + c.utf8Size }
          | none => s
    | none =>
        match s.peekChar? with
        | some c => skipUntilRecoveryFn { s with pos := s.pos + c.utf8Size }
        | none => s

partial def manyRecoverFn (p : ParserFn) : ParserFn := fun s =>
  if s.pos ≥ s.input.utf8ByteSize then s
  else
    let s := triviaFn s
    if s.pos ≥ s.input.utf8ByteSize then s
    else
      let cmdStart := s.pos
      let iniSz := s.stackSize
      let s' := p s
      if s'.hasError then
        let err := s'.errorMsg.get!
        let s' := { s' with errors := s'.errors.push err, errorMsg := none }
        let s' := s'.shrinkStack iniSz
        let s' := skipUntilRecoveryFn s'
        let s' :=
          if s'.pos == cmdStart && s'.pos < s'.input.utf8ByteSize then
            advanceCharFn s'
          else s'
        let endPos := s'.pos
        let s' :=
          if cmdStart < endPos then
            let skipped := String.Pos.Raw.extract s'.input ⟨cmdStart⟩ ⟨endPos⟩
            s'.pushSyntax (.token `skipped skipped)
          else s'
        manyRecoverFn p s'
      else manyRecoverFn p s'

@[inline] def pushNullFn : ParserFn := fun s => s.pushSyntax (.node `null #[])

def sep1Fn (p sep : ParserFn) : ParserFn := fun s =>
  let s := p s
  if s.hasError then s else manyFn (atomicFn (sep >> p)) s

@[inline] def commaSep1Fn (p : ParserFn) : ParserFn :=
  sep1Fn p (triviaFn >> symbolFn "," >> triviaFn)

@[inline] def wsSep1Fn (p : ParserFn) : ParserFn :=
  sep1Fn p triviaFn

def holeFn : ParserFn :=
  nodeFn `Lean.Parser.Term.hole (symbolFn "_")

def binderNameFn : ParserFn := fun s =>
  match peekTok s with
  | .atom "_" => holeFn s
  | _         => identRawFn s

mutual

partial def levelAtomFn : ParserFn := fun s =>
  match s.peekChar? with
  | some '(' =>
      nodeFn `Lean.Parser.Level.paren
        (symbolFn "(" >> triviaFn >> levelFn >> triviaFn >> symbolFn ")") s
  | some ch =>
      if ch.isDigit then
        nodeFn `Lean.Parser.Level.num numRawFn s
      else
        let (id?, s) := peekIdentStr s
        match id? with
        | some "max" =>
            nodeFn `Lean.Parser.Level.max
              (symbolFn "max" >> wsFn >> sep1Fn levelAtomFn triviaFn) s
        | some name =>
            if isReserved name then s.setError "expected level"
            else nodeFn `Lean.Parser.Level.ident identRawFn s
        | none => s.setError "expected level"
  | none => s.setError "expected level"

partial def levelFn : ParserFn := fun s =>
  let iniSz := s.stackSize
  let s := levelAtomFn s
  if s.hasError then s
  else
    let iniPos := s.pos
    let s' := atomicFn (triviaFn >> symbolFn "+" >> triviaFn >> numRawFn) s
    if s'.hasError && s'.pos == iniPos then s'.restore (iniSz + 1) iniPos
    else if s'.hasError then s'
    else s'.mkNode `Lean.Parser.Level.addLit iniSz

partial def univParamsFn : ParserFn :=
  optionalFn (atomicFn
    (nodeFn `Lean.Parser.Command.univParams
      (symbolFn "." >> symbolFn "{" >> triviaFn >> sep1Fn identRawFn (triviaFn >> symbolFn "," >> triviaFn) >> triviaFn >> symbolFn "}")))

partial def univArgsFn : ParserFn :=
  optionalFn (atomicFn
    (nodeFn `Lean.Parser.Term.univArgs
      (symbolFn "." >> symbolFn "{" >> triviaFn >> sep1Fn levelFn (triviaFn >> symbolFn "," >> triviaFn) >> triviaFn >> symbolFn "}")))

partial def explicitBinderFn : ParserFn :=
  nodeFn `Lean.Parser.Term.explicitBinder
    (symbolFn "(" >> triviaFn >> sep1Fn binderNameFn triviaFn >> triviaFn >>
     optionalFn (symbolFn ":" >> triviaFn >> termFn >> triviaFn) >> symbolFn ")")

partial def implicitBinderFn : ParserFn :=
  nodeFn `Lean.Parser.Term.implicitBinder
    (symbolFn "{" >> triviaFn >> sep1Fn binderNameFn triviaFn >> triviaFn >>
     optionalFn (symbolFn ":" >> triviaFn >> termFn >> triviaFn) >> symbolFn "}")

partial def explicitBinderTypedFn : ParserFn :=
  nodeFn `Lean.Parser.Term.explicitBinder
    (symbolFn "(" >> triviaFn >> sep1Fn binderNameFn triviaFn >> triviaFn >>
     symbolFn ":" >> triviaFn >> termFn >> triviaFn >> symbolFn ")")

partial def implicitBinderTypedFn : ParserFn :=
  nodeFn `Lean.Parser.Term.implicitBinder
    (symbolFn "{" >> triviaFn >> sep1Fn binderNameFn triviaFn >> triviaFn >>
     symbolFn ":" >> triviaFn >> termFn >> triviaFn >> symbolFn "}")

partial def binderFn : ParserFn := fun s =>
  match s.peekChar? with
  | some '{' => implicitBinderFn s
  | some '(' => explicitBinderFn s
  | _ => binderNameFn s

partial def termFn : ParserFn := prattFn 0

partial def prattFn (minPrec : Nat) : ParserFn := fun s =>
  let s := leadingFn minPrec s
  if s.hasError then s else prattLoopFn minPrec s

partial def prattLoopFn (minPrec : Nat) (s : State) : State :=
  let iniSz := s.stackSize
  let iniPos := s.pos
  let s' := trailingFn minPrec s
  if s'.hasError then
    s'.restore (iniSz - 1) iniPos
  else if s'.pos == iniPos && s'.stackSize == iniSz then
    s'.setPos iniPos
  else if s'.pos == iniPos then
    { s' with stack := s'.stack.shrink iniSz, pos := iniPos }
  else
    prattLoopFn minPrec s'

partial def leadingFn (_minPrec : Nat) : ParserFn := fun s =>
  if s.pos ≥ s.input.utf8ByteSize then s.setError "expected expression"
  else
    if peekTok s == .atom "_" then holeFn s
    else
    let (id?, s) := peekIdentStr s
    match id? with
    | some "fun" => parseLamFn s
    | some "let" => parseLetFn s
    | some "sorry" => parseSorryFn s
    | some "Type" => parseTypeFn s
    | _ =>
        match s.peekChar? with
        | some '(' => (atomicFn parseUnitFn <|> parseParenOrPiFn) s
        | some '{' => parseImplicitDepArrowFn s
        | some '@' => parseExplicitAppFn s
        | some c =>
            if c.isDigit then
              nodeFn `Lean.Parser.Term.num numRawFn s
            else
              parseIdentWithUnivFn s
        | none => s.setError "expected expression"

partial def trailingFn (minPrec : Nat) (s : State) : State :=
  let iniSz := s.stackSize
  let iniPos := s.pos
  let sTrivia := triviaFn s
  let triviaProgressed := sTrivia.pos > iniPos
  let stop := sTrivia.restore iniSz iniPos
  let infixOp (sym : String) (gate rprec : Nat) (kind : SyntaxNodeKind) : State :=
    if minPrec > gate then stop
    else
      let s' := (symbolFn sym >> triviaFn >> prattFn rprec) sTrivia
      if s'.hasError then s' else s'.mkNode kind (iniSz - 1)
  let app : State :=
    if !triviaProgressed then stop
    else tryAppArgFn minPrec iniSz iniPos sTrivia
  match peekTok sTrivia with
  | .atom "->"    => infixOp "->" 25 25 `Lean.Parser.Term.arrow
  | .atom "→"     => infixOp "→"  25 25 `Lean.Parser.Term.arrow
  | .atom "="     => infixOp "="  50 51 `«term_=_»
  | .atom "+"     => infixOp "+"  65 66 `«term_+_»
  | .ident _ | .num _ | .atom "(" | .atom "_" | .atom "sorry" | .atom "Type" | .atom "@" => app
  | _             => stop

partial def tryAppArgFn (minPrec : Nat) (iniSz iniPos : Nat) (s : State) : State :=
  if minPrec > 1024 then s.restore iniSz iniPos
  else
    let argStart := s.pos
    let sArg := atomArgFn s
    if sArg.hasError then
      if sArg.pos == argStart then sArg.restore iniSz iniPos
      else sArg
    else sArg.mkNode `Lean.Parser.Term.app (iniSz - 1)

partial def atomArgFn : ParserFn := fun s =>
  if peekTok s == .atom "_" then holeFn s
  else
  let (id?, s) := peekIdentStr s
  match id? with
  | some "sorry" => parseSorryFn s
  | some "Type" => parseTypeAtomFn s
  | some name =>
      if isReserved name then s.setError "keyword"
      else parseIdentWithUnivFn s
  | none =>
      match s.peekChar? with
      | some '(' => (atomicFn parseUnitFn <|> parseParenFn) s
      | some '@' => parseExplicitAppFn s
      | some c =>
          if c.isDigit then nodeFn `Lean.Parser.Term.num numRawFn s
          else s.setError "expected argument"
      | none => s.setError "expected argument"

partial def parseExplicitAppFn : ParserFn :=
  nodeFn `Lean.Parser.Term.explicit
    (symbolFn "@" >> parseIdentWithUnivFn)

partial def parseIdentWithUnivFn : ParserFn := fun s =>
  let iniSz := s.stackSize
  let s := identRawFn s
  if s.hasError then s
  else
    let s := univArgsFn s
    if s.hasError then s
    else if s.stackSize == iniSz + 1 then
      s.mkNode `Lean.Parser.Term.ident iniSz
    else
      s.mkNode `Lean.Parser.Term.explicitUniv iniSz

partial def parseLamFn : ParserFn :=
  nodeFn `Lean.Parser.Term.fun
    (symbolFn "fun" >> wsFn >> sep1Fn parseFunBinderFn triviaFn >> triviaFn >>
     optionalFn (symbolFn ":" >> triviaFn >> termFn >> triviaFn) >>
     (atomicFn (symbolFn "=>") <|> symbolFn "⇒") >> triviaFn >> termFn)

partial def parseFunBinderFn : ParserFn := fun s =>
  match s.peekChar? with
  | some '(' => explicitBinderFn s
  | some '{' => implicitBinderFn s
  | _ => binderNameFn s

partial def optTypeAnnotFn : ParserFn := fun s =>
  match peekTok s with
  | .atom ":" => (symbolFn ":" >> triviaFn >> termFn >> triviaFn) s
  | _ => s

partial def parseLetFn : ParserFn :=
  nodeFn `Lean.Parser.Term.let
    (symbolFn "let" >> wsFn >> identRawFn >> triviaFn >> optTypeAnnotFn >>
     symbolFn ":=" >> triviaFn >> termFn >> triviaFn >> symbolFn ";" >> triviaFn >> termFn)

partial def parseSorryFn : ParserFn :=
  nodeFn `Lean.Parser.Term.sorry (symbolFn "sorry")

partial def optLevelFn : ParserFn := fun s =>
  let iniSz := s.stackSize
  let iniPos := s.pos
  let s' := atomicFn (wsFn >> levelFn) s
  if s'.hasError && s'.pos == iniPos then s'.restore iniSz iniPos else s'

partial def parseTypeFn : ParserFn :=
  nodeFn `Lean.Parser.Term.type (symbolFn "Type" >> optLevelFn)

partial def parseTypeAtomFn : ParserFn :=
  nodeFn `Lean.Parser.Term.type (symbolFn "Type")

partial def parseUnitFn : ParserFn :=
  nodeFn `Lean.Parser.Term.unit (symbolFn "(" >> triviaFn >> symbolFn ")")

partial def parseParenFn : ParserFn := fun s =>
  let iniSz := s.stackSize
  let s := (symbolFn "(" >> triviaFn >> termFn >> triviaFn) s
  if s.hasError then s.mkNode `Lean.Parser.Term.paren iniSz
  else
    match s.peekChar? with
    | some ':' =>
        let s := (symbolFn ":" >> triviaFn >> termFn >> triviaFn >> symbolFn ")") s
        s.mkNode `Lean.Parser.Term.typeAscription iniSz
    | _ =>
        let s := symbolFn ")" s
        s.mkNode `Lean.Parser.Term.paren iniSz

partial def parseDepArrowFn : ParserFn :=
  nodeFn `Lean.Parser.Term.depArrow
    (explicitBinderTypedFn >> triviaFn >>
     (atomicFn (symbolFn "->") <|> symbolFn "→") >> triviaFn >> prattFn 25)

partial def parseImplicitDepArrowFn : ParserFn :=
  nodeFn `Lean.Parser.Term.depArrow
    (implicitBinderTypedFn >> triviaFn >>
     (atomicFn (symbolFn "->") <|> symbolFn "→") >> triviaFn >> prattFn 25)

partial def parseParenOrPiFn : ParserFn :=
  atomicFn parseDepArrowFn <|> parseParenFn

end

def declIdFn : ParserFn :=
  nodeFn `Lean.Parser.Command.declId (identRawFn >> univParamsFn)

def typeSigFn : ParserFn :=
  wsFn >> symbolFn ":" >> triviaFn >> termFn

def optTypeSigFn : ParserFn := optionalFn (atomicFn typeSigFn)

def optDeclSigFn : ParserFn :=
  nodeFn `Lean.Parser.Command.optDeclSig
    (manyFn (atomicFn (triviaFn >> binderFn)) >> optTypeSigFn)

def declSigFn : ParserFn :=
  nodeFn `Lean.Parser.Command.declSig
    (manyFn (atomicFn (triviaFn >> binderFn)) >> triviaFn >> symbolFn ":" >> triviaFn >> termFn)

def declValSimpleFn : ParserFn :=
  nodeFn `Lean.Parser.Command.declValSimple (symbolFn ":=" >> triviaFn >> termFn)

def parseDefinitionFn : ParserFn :=
  nodeFn `Lean.Parser.Command.definition
    (symbolFn "def" >> wsFn >> declIdFn >> optDeclSigFn >> triviaFn >> declValSimpleFn)

def parseExampleFn : ParserFn :=
  nodeFn `Lean.Parser.Command.example
    (symbolFn "example" >> optDeclSigFn >> triviaFn >> declValSimpleFn)

def parseAxiomFn : ParserFn :=
  nodeFn `Lean.Parser.Command.axiom
    (symbolFn "axiom" >> wsFn >> declIdFn >> declSigFn)

def parseCtorFn : ParserFn :=
  nodeFn `Lean.Parser.Command.ctor
    (symbolFn "|" >> triviaFn >> identRawFn >> optDeclSigFn)

def parseInductiveFn : ParserFn :=
  nodeFn `Lean.Parser.Command.inductive
    (symbolFn "inductive" >> wsFn >> declIdFn >> optDeclSigFn >> triviaFn >>
     optionalFn (atomicFn (symbolFn "where")) >> triviaFn >>
     optionalFn (atomicFn parseCtorFn) >>
     manyFn (atomicFn (triviaFn >> parseCtorFn)))

def parseStructFieldFn : ParserFn :=
  nodeFn `Lean.Parser.Command.structField
    (symbolFn "(" >> triviaFn >> identRawFn >> optDeclSigFn >> triviaFn >> symbolFn ")")

def parseStructureFn : ParserFn :=
  nodeFn `Lean.Parser.Command.structure
    (symbolFn "structure" >> wsFn >> declIdFn >> optDeclSigFn >> triviaFn >>
     symbolFn "where" >> manyFn (atomicFn (triviaFn >> parseStructFieldFn)))

def parseImportFn : ParserFn :=
  nodeFn `Lean.Parser.Command.import (symbolFn "import" >> wsFn >> identRawFn)

def parseCommandFn : ParserFn := fun s =>
  let (id?, s) := peekIdentStr s
  match id? with
  | some "def" => parseDefinitionFn s
  | some "example" => parseExampleFn s
  | some "axiom" => parseAxiomFn s
  | some "inductive" => parseInductiveFn s
  | some "structure" => parseStructureFn s
  | _ => s.setError "expected command"

def parseHeaderFn : ParserFn :=
  nodeFn `Lean.Parser.Module.header (manyFn (atomicFn (triviaFn >> parseImportFn)))

def parseProgramFn : ParserFn :=
  nodeFn `Lean.Parser.Module (parseHeaderFn >> manyRecoverFn parseCommandFn)

def parse (input : String) : Cst × Array ParseError :=
  let init : State := {
    input, pos := 0, stack := #[], errors := #[], errorMsg := none,
    identCache := { startPos := input.utf8ByteSize + 1, stopPos := 0, value := "" }
  }
  let s := parseProgramFn init
  let cst := s.stack.back? |>.getD (.token `missing input)
  let errs := match s.errorMsg with
    | some e => s.errors.push e
    | none => s.errors
  (cst, errs)

end Qdt.Frontend.Parser
