import Qdt.Frontend.Cst
import Qdt.MLTT.Universe

namespace Qdt.Frontend.Parser

open Lean (Name)
open Cst

structure ParseError where
  msg : String
  pos : String.Pos.Raw
deriving Repr, Inhabited

private structure State where
  input : String
  pos : String.Pos.Raw
deriving Inhabited

private abbrev ParserM := StateT State (Except ParseError)

private def initState (input : String) : State :=
  { input, pos := ⟨0⟩ }

private def Src.mk (startPos endPos : String.Pos.Raw) : Src :=
  some ⟨startPos, endPos⟩

private def getPos : ParserM String.Pos.Raw := return (← get).pos

private def setPos (pos : String.Pos.Raw) : ParserM Unit := modify fun st => { st with pos }

private def isEof : ParserM Bool := do
  let st ← get
  return st.pos == st.input.rawEndPos

private def peekChar? : ParserM (Option Char) := do
  let st ← get
  return String.Pos.Raw.get? st.input st.pos

private def peekNextChar? : ParserM (Option Char) := do
  let st ← get
  if st.pos == st.input.rawEndPos then
    return none
  else
    let nextPos := String.Pos.Raw.next st.input st.pos
    return String.Pos.Raw.get? st.input nextPos

private def fail {α : Type} (msg : String) : ParserM α := do
  throw ⟨msg, ← getPos⟩

private def optional {α : Type} (p : ParserM α) : ParserM (Option α) :=
  (return some (← p)) <|> return none

mutual

private partial def many {α : Type} (p : ParserM α) : ParserM (List α) :=
  many1 p <|> return []

private partial def many1 {α : Type} (p : ParserM α) : ParserM (List α) := do
  return (← p) :: (← many p)

end

private def choice {α : Type} (ps : List (ParserM α)) : ParserM α → ParserM α :=
  ps.foldr (· <|> ·)

private def advanceChar : ParserM Unit := do
  let st ← get
  if st.pos == st.input.rawEndPos then
    fail "Unexpected end of input"
  else
    set { st with pos := String.Pos.Raw.next st.input st.pos }

private partial def skipLine : ParserM Unit := do
  if ← isEof then
    return
  else
    match ← peekChar? with
    | some '\n' => advanceChar
    | _ =>
        advanceChar
        skipLine

private partial def skipBlock (depth : Nat) : ParserM Unit := do
  if ← isEof then
    fail "Unterminated comment"
  else
    match ← peekChar?, ← peekNextChar? with
    | some '/', some '-' =>
        advanceChar
        advanceChar
        skipBlock (depth + 1)
    | some '-', some '/' =>
        advanceChar
        advanceChar
        if depth == 1 then
          return
        else
          skipBlock (depth - 1)
    | _, _ =>
        advanceChar
        skipBlock depth

private partial def ws : ParserM Unit := do
  if ← isEof then
    return
  else
    match ← peekChar?, ← peekNextChar? with
    | some c, _ =>
        if c.isWhitespace then
          advanceChar
          ws
        else
          match c, ← peekNextChar? with
          | '-', some '-' =>
              advanceChar
              advanceChar
              skipLine
              ws
          | '/', some '-' =>
              advanceChar
              advanceChar
              skipBlock 1
              ws
          | _, _ =>
              return
    | none, _ =>
        return

private def kw : List String :=
  [
    "fun",
    "let",
    "def",
    "example",
    "axiom",
    "inductive",
    "structure",
    "where",
    "import",
  ]

private def isIdentChar : Char → Bool :=
  fun c => c.isAlphanum || c == '_' || c == '\'' || c == '.'

private def isIdentStart : Char → Bool :=
  fun c => c.isAlpha || c == '_' || c == '\''

private partial def readIdent : ParserM String := do
  let some c ← peekChar? | fail "expected identifier"
  if !isIdentStart c then
    fail "expected identifier"
  else
    let mut acc := ""
    acc := acc.push c
    advanceChar
    while true do
      match ← peekChar? with
      | some '.' =>
          let st ← get
          advanceChar
          match ← peekChar? with
          | some '{' =>
              set st
              break
          | _ => acc := acc.push '.'
      | some c' =>
          if isIdentChar c' then
            acc := acc.push c'
            advanceChar
          else
            break
      | none =>
          break
    return acc

private def Name.ofString : String → Name :=
  fun s => s.splitOn "." |>.foldl Name.str Name.anonymous

-- Token parser: consumes string WITHOUT leading/trailing whitespace
private def tok (s : String) : ParserM Unit := do
  let expected := s.toList
  let rec loop : List Char → ParserM Unit
    | [] => return
    | c :: cs => do
        match ← peekChar? with
        | none =>
            fail s!"unexpected end of input, expected '{s}'"
        | some c' =>
            if c' == c then
              advanceChar
              loop cs
            else
              fail s!"expected '{s}'"
  loop expected

-- String parser: ws before, then token (no trailing ws)
private def str (s : String) : ParserM Unit := do
  ws
  tok s

private def keyword (kw : String) : ParserM Unit := str kw
private def arrow : ParserM Unit := str "->" <|> str "→"
-- private def times : ParserM Unit := str "×"

private def parseNat : ParserM Nat := do
  ws
  let some c ← peekChar? | fail "expected numeral"
  if !c.isDigit then
    fail "expected numeral"
  else
    let mut acc : Nat := 0
    while true do
      match ← peekChar? with
      | some d =>
          if d.isDigit then
            acc := acc * 10 + (d.toNat - '0'.toNat)
            advanceChar
          else
            break
      | none =>
          break
    return acc

private def natToUniverse : Nat → Universe
  | 0 => .zero
  | n + 1 => .succ (natToUniverse n)

private def parseIdentStr : ParserM (Src × String) := do
  ws
  let startPos ← getPos
  let name ← readIdent
  let endPos ← getPos
  return (Src.mk startPos endPos, name)

private def parseIdent : ParserM (Src × Name) := do
  let (src, s) ← parseIdentStr
  pure (src, Name.ofString s)

private inductive Prec
  | min
  | letE
  | funE
  | pi
  | eq
  | addL
  | addR
  | mulL
  | mulR
  | app
  | max
deriving Repr, Inhabited, DecidableEq, Ord

private def srcStartPos (src : Src) : String.Pos.Raw :=
  src.map Span.startPos |>.getD (String.Pos.Raw.mk 0)

private def srcEndPos (src : Src) : String.Pos.Raw :=
  src.map Span.endPos |>.getD (String.Pos.Raw.mk 0)

private def termStartPos : Term → String.Pos.Raw
  | .missing src
  | .ident src _ _
  | .app src _ _
  | .lam src _ _
  | .pi src _ _
  | .arrow src _ _
  | .letE src _ _ _ _
  | .u src _
  | .eq src _ _
  | .natLit src _
  | .add src _ _
  | .sub src _ _
  | .mul src _ _
  | .ann src _ _
  | .sorry src =>
     srcStartPos src

private def termEndPos : Term → String.Pos.Raw
  | .missing src
  | .ident src _ _
  | .app src _ _
  | .lam src _ _
  | .pi src _ _
  | .arrow src _ _
  | .letE src _ _ _ _
  | .u src _
  | .eq src _ _
  | .natLit src _
  | .add src _ _
  | .sub src _ _
  | .mul src _ _
  | .ann src _ _
  | .sorry src =>
     srcEndPos src

private def levelKeywords : List String :=
  ["fun", "let", "def", "example", "axiom", "inductive", "structure", "where", "import", "sorry"]

private def peekIdent : ParserM (Option String) := do
  let st ← get
  let startPos := st.pos
  if let some c ← peekChar? then
    if isIdentStart c then
      let name ← readIdent
      set { st with pos := startPos }
      return some name
  return none

mutual

private partial def parseTypedBinderGroup : ParserM TypedBinderGroup := do
  ws
  let startPos ← getPos
  str "("
  let names ← many1 parseBinderNameWithSrc
  str ":"
  let ty ← parsePreterm
  str ")"
  let endPos ← getPos
  return .mk (Src.mk startPos endPos) names ty

private partial def parseBinderNameWithSrc : ParserM (Src × Name) := do
  let (src, name) ← parseIdentStr
  if name == "_" then
    pure (src, Name.anonymous)
  else
    pure (src, Name.ofString name)

private partial def parseBinderName : ParserM Name := do
  let (_, name) ← parseBinderNameWithSrc
  pure name

private partial def parseUniverseAtom : ParserM Universe := do
  ws
  let some c ← peekChar? | fail "expected universe level"
  if c == '(' then
    advanceChar
    let u ← parseUniverseLevel
    str ")"
    return u
  else if c.isDigit then
    let n ← parseNat
    return natToUniverse n
  else if let some name ← peekIdent then
    if name == "max" then
      let _ ← readIdent
      let u₁ ← parseUniverseAtom
      let u₂ ← parseUniverseAtom
      let rest ← many parseUniverseAtom
      return rest.foldl Universe.max (.max u₁ u₂)
    else if !levelKeywords.contains name then
      let _ ← readIdent
      return .level (Name.ofString name)
    else
      fail "expected universe level"
  else
    fail "expected universe level"

private partial def parseUniverseLevel : ParserM Universe := do
  let base ← parseUniverseAtom
  -- Save position before trying to consume whitespace for '+'
  let posBeforeWs ← getPos
  ws
  match ← peekChar? with
  | some '+' =>
      advanceChar
      let n ← parseNat
      if n == 0 then
        fail "successor offset must be > 0"
      let mut u := base
      for _ in List.range n do
        u := .succ u
      return u
  | _ =>
      -- No '+', restore position to before whitespace
      setPos posBeforeWs
      return base

private partial def parseUnivParams : ParserM (List Name) := do
  ws
  match ← peekChar? with
  | some '.' =>
      advanceChar
      match ← peekChar? with
      | some '{' =>
          advanceChar
          ws
          match ← peekChar? with
          | some '}' => fail "universe parameter list cannot be empty"
          | _ =>
              let first ← parseBinderName
              let rest ← many (str "," *> parseBinderName)
              str "}"
              return first :: rest
      | _ => fail "expected '{' after '.'"
  | _ => return []

private partial def parseUnivArgs : ParserM (List Universe) := do
  ws
  match ← peekChar? with
  | some '.' =>
      advanceChar
      match ← peekChar? with
      | some '{' =>
          advanceChar
          ws
          match ← peekChar? with
          | some '}' => fail "universe argument list cannot be empty"
          | _ =>
              let first ← parseUniverseLevel
              let rest ← many (str "," *> parseUniverseLevel)
              str "}"
              return first :: rest
      | _ => fail "expected '{' after '.'"
  | _ => return []

private partial def parseBinderGroup : ParserM BinderGroup :=
  (do
    let group ← parseTypedBinderGroup
    pure (.typed group)) <|>
  (do
    ws
    let startPos ← getPos
    let name ← parseBinderName
    let endPos ← getPos
    pure (.untyped (Src.mk startPos endPos) name))

private partial def parseLambdaLeading : ParserM Term := do
  ws
  let startPos ← getPos
  keyword "fun"
  let binders ← many1 parseBinderGroup
  keyword "=>"
  let body ← parsePreterm
  let endPos := termEndPos body
  return .lam (Src.mk startPos endPos) binders body

private partial def parseLetLeading : ParserM Term := do
  ws
  let startPos ← getPos
  keyword "let"
  let (_src, name) ← parseIdent
  let tyOpt ← optional (str ":" *> parsePreterm)
  keyword ":="
  let rhs ← parsePreterm
  str ";"
  let body ← parsePreterm
  let endPos := termEndPos body
  return .letE (Src.mk startPos endPos) name tyOpt rhs body

private partial def parsePiLeading : ParserM Term := do
  ws
  let startPos ← getPos
  let group ← parseTypedBinderGroup
  arrow
  let b ← prattParser .pi
  let endPos := termEndPos b
  return .pi (Src.mk startPos endPos) group b

-- private partial def parseSigmaLeading : ParserM Term := do
--   ws
--   let startPos ← getPos
--   let group ← parseTypedBinderGroup
--   times
--   let b ← prattParser .pi
--   let endPos := termEndPos b
--   return .sigma (Src.mk startPos endPos) group b

private partial def parseUnit : ParserM Term := do
  ws
  let startPos ← getPos
  str "("
  ws
  match ← peekChar? with
  | some ')' =>
      advanceChar
      let endPos ← getPos
      return .ident (Src.mk startPos endPos) (Name.ofString "Unit.unit") []
  | _ =>
      fail "expected unit"

private partial def parseAnnPairParen : ParserM Term := do
  ws
  let startPos ← getPos
  str "("
  let e ← parsePreterm
  ws
  match ← peekChar? with
  -- | some ',' =>
  --     str ","
  --     let b ← parsePreterm
  --     str ")"
  --     let endPos ← getPos
  --     return .pair (Src.mk startPos endPos) e b
  | some ':' =>
      str ":"
      let ty ← parsePreterm
      str ")"
      let endPos ← getPos
      return .ann (Src.mk startPos endPos) e ty
  | _ =>
      str ")"
      pure e

private partial def parseSorry : ParserM Term := do
  ws
  let startPos ← getPos
  keyword "sorry"
  let endPos ← getPos
  return .sorry (Src.mk startPos endPos)

private partial def parseType : ParserM Term := do
  ws
  let startPos ← getPos
  keyword "Type"
  let endPos ← getPos
  return .u (Src.mk startPos endPos) .zero

private partial def parseNatLit : ParserM Term := do
  ws
  let startPos ← getPos
  let n ← parseNat
  let endPos ← getPos
  return .natLit (Src.mk startPos endPos) n

private partial def parseIdentAtom : ParserM Term := do
  ws
  let startPos ← getPos
  let nameStr ← readIdent
  let afterIdent ← getPos
  if kw.contains nameStr then
    fail "keyword in expression"
  else
    let univs ← parseUnivArgs
    let endPos ←
      if univs.isEmpty then pure afterIdent else getPos
    return .ident (Src.mk startPos endPos) (Name.ofString nameStr) univs

private partial def parseAtomLeading : ParserM Term := do
  if ← isEof then
    fail "unexpected end of input"
  else
    choice
      [
        parseUnit,
        parseAnnPairParen,
        parseSorry,
        parseType,
        parseNatLit,
        parseIdentAtom,
      ]
      (fail "expected atom")

private partial def prattParser (minPrec : Prec) : ParserM Term := do
  let leadingParsers : List (Prec × ParserM Term) :=
    [
      (.max, parsePiLeading),
      -- (.max, parseSigmaLeading),
      (.max, parseAtomLeading),
      (.funE, parseLambdaLeading),
      (.letE, parseLetLeading),
    ]

  let trailingParsers : List (Prec × Prec × (Prec → Term → ParserM Term)) :=
    [
      (.app, .app, parseTypeLevelTrailing),
      (.app, .app, parseAppTrailing),
      (.mulL, .mulR, parseMulTrailing),
      (.addL, .addR, parseAddTrailing),
      (.eq, .eq, parseEqTrailing),
      -- (.pi, .pi, parseProdTrailing),
      (.pi, .pi, parseArrowTrailing),
    ]

  ws

  let rec tryLeading : List (Prec × ParserM Term) → ParserM Term
    | [] => fail "expected expression"
    | (pPrec, p) :: ps =>
        if compare pPrec minPrec |>.isGE then
          p <|> tryLeading ps
        else
          tryLeading ps

  let left ← tryLeading leadingParsers

  let rec parseTrailing (left : Term) : ParserM Term := do
    let rec tryTrailing : List (Prec × Prec × (Prec → Term → ParserM Term)) → ParserM Term
      | [] => pure left
      | (leftPrec, rightPrec, p) :: ps =>
          if compare leftPrec minPrec |>.isGE then
            ((p rightPrec left) >>= parseTrailing) <|> tryTrailing ps
          else
            tryTrailing ps
    tryTrailing trailingParsers

  parseTrailing left

private partial def parsePreterm : ParserM Term :=
  prattParser .min

private partial def parseTypeLevelTrailing (_rightPrec : Prec) (left : Term) : ParserM Term := do
  ws
  match left with
  | .u src .zero =>
      let some c ← peekChar? | fail "no universe level"
      if c == '(' then
        let lvl ← parseUniverseLevel
        let endPos ← getPos
        let startPos := srcStartPos src
        return .u (Src.mk startPos endPos) lvl
      else
        let st ← get
        let lvl? ←
          (try
            let lvl ← parseUniverseLevel
            pure (some lvl)
          catch _ =>
            pure none)
        match lvl? with
        | none =>
            set st
            fail "no universe level"
        | some lvl =>
            let endPos ← getPos
            let startPos := srcStartPos src
            return .u (Src.mk startPos endPos) lvl
  | _ =>
      fail "not Type"

private partial def parseAppTrailing (_rightPrec : Prec) (left : Term) : ParserM Term :=
  (do
      let arg ← parseLambdaLeading
      let startPos := termStartPos left
      let endPos := termEndPos arg
      return .app (Src.mk startPos endPos) left arg) <|>
  (do
      let arg ← parseLetLeading
      let startPos := termStartPos left
      let endPos := termEndPos arg
      return .app (Src.mk startPos endPos) left arg) <|>
  (do
      let arg ← parseAtomLeading
      let startPos := termStartPos left
      let endPos := termEndPos arg
      return .app (Src.mk startPos endPos) left arg)

private partial def parseMulTrailing (rightPrec : Prec) (left : Term) : ParserM Term := do
  ws
  match ← peekChar? with
  | some '*' =>
      advanceChar
      let b ← prattParser rightPrec
      let startPos := termStartPos left
      let endPos := termEndPos b
      return .mul (Src.mk startPos endPos) left b
  | _ =>
      fail "expected *"

private partial def parseAddTrailing (rightPrec : Prec) (left : Term) : ParserM Term := do
  ws
  match ← peekChar? with
  | some '+' =>
      advanceChar
      let b ← prattParser rightPrec
      let startPos := termStartPos left
      let endPos := termEndPos b
      return .add (Src.mk startPos endPos) left b
  | some '-' =>
      advanceChar
      let b ← prattParser rightPrec
      let startPos := termStartPos left
      let endPos := termEndPos b
      return .sub (Src.mk startPos endPos) left b
  | _ =>
      fail "expected + or -"

private partial def parseEqTrailing (rightPrec : Prec) (left : Term) : ParserM Term := do
  ws
  match ← peekChar? with
  | some '=' =>
      advanceChar
      let b ← prattParser rightPrec
      let startPos := termStartPos left
      let endPos := termEndPos b
      return .eq (Src.mk startPos endPos) left b
  | _ =>
      fail "expected ="

-- private partial def parseProdTrailing (rightPrec : Prec) (left : Term) : ParserM Term := do
--   times
--   let b ← prattParser rightPrec
--   let startPos := termStartPos left
--   let endPos := termEndPos b
--   return .prod (Src.mk startPos endPos) left b

private partial def parseArrowTrailing (rightPrec : Prec) (left : Term) : ParserM Term := do
  arrow
  let b ← prattParser rightPrec
  let startPos := termStartPos left
  let endPos := termEndPos b
  return .arrow (Src.mk startPos endPos) left b

end

private def parseParams : ParserM (List TypedBinderGroup) :=
  many parseTypedBinderGroup

private def parseConstructor : ParserM Command.InductiveConstructor := do
  ws
  let startPos ← getPos
  str "|"
  let (_src, name) ← parseIdent
  let fields ← parseParams
  let tyOpt ← optional (str ":" *> parsePreterm)
  let endPos ← getPos
  pure
    {
      src := Src.mk startPos endPos
      name
      fields
      tyOpt
    }

private def parseInductive : ParserM Command.Cmd := do
  ws
  let startPos ← getPos
  keyword "inductive"
  let (_src, name) ← parseIdent
  let univParams ← parseUnivParams
  let params ← parseParams
  let tyOpt ← optional (str ":" *> parsePreterm)
  keyword "where"
  let ctors ← many parseConstructor
  let endPos ← getPos
  return .inductive
      {
        src := Src.mk startPos endPos
        name
        univParams
        params
        tyOpt
        ctors
      }

private def parseField : ParserM Command.StructureField := do
  ws
  let startPos ← getPos
  str "("
  let (nameSrc, nameStr) ← parseIdentStr
  if nameStr.contains '.' then
    fail "Structure field names must be atomic"
  else
    let name := Name.ofString nameStr
    let params ← parseParams
    str ":"
    let ty ← parsePreterm
    str ")"
    let endPos ← getPos
    pure
      {
        src := Src.mk startPos endPos
        nameSrc
        name
        params
        ty
      }

private def parseStructure : ParserM Command.Cmd := do
  ws
  let startPos ← getPos
  keyword "structure"
  let (_src, name) ← parseIdent
  let univParams ← parseUnivParams
  let params ← parseParams
  let tyOpt ←
    optional (do
      str ":"
      parsePreterm)
  keyword "where"
  let fields ← many parseField
  let endPos ← getPos
  return .structure
      {
        src := Src.mk startPos endPos
        name
        univParams
        params
        tyOpt
        fields
      }

private def parseDefBody : ParserM (List TypedBinderGroup × Option Term × Term) := do
  let params ← parseParams
  let retTyOpt ←
    optional (do
      str ":"
      parsePreterm)
  keyword ":="
  let body ← parsePreterm
  pure (params, retTyOpt, body)

private def parseDef : ParserM Command.Cmd := do
  ws
  let startPos ← getPos
  keyword "def"
  let (_src, name) ← parseIdent
  let univParams ← parseUnivParams
  let (params, tyOpt, body) ← parseDefBody
  let endPos ← getPos
  return .definition
      {
        src := Src.mk startPos endPos
        name
        univParams
        params
        tyOpt
        body
      }

private def parseExample : ParserM Command.Cmd := do
  ws
  let startPos ← getPos
  keyword "example"
  let univParams ← parseUnivParams
  let (params, tyOpt, body) ← parseDefBody
  let endPos ← getPos
  return .example
      {
        src := Src.mk startPos endPos
        univParams
        params
        tyOpt
        body
      }

private def parseAxiom : ParserM Command.Cmd := do
  ws
  let startPos ← getPos
  keyword "axiom"
  let (_src, name) ← parseIdent
  let univParams ← parseUnivParams
  let params ← parseParams
  str ":"
  let ty ← parsePreterm
  let endPos ← getPos
  return .axiom
      {
        src := Src.mk startPos endPos
        name
        univParams
        params
        ty
      }

private def parseImport : ParserM Command.Cmd := do
  ws
  let startPos ← getPos
  keyword "import"
  let (_src, moduleName) ← parseIdent
  let endPos ← getPos
  return .import
      {
        src := Src.mk startPos endPos
        moduleName
      }

private def parseItem : ParserM Command.Cmd :=
  choice
    [
      parseImport,
      parseDef,
      parseExample,
      parseAxiom,
      parseInductive,
      parseStructure,
    ]
    (fail "unexpected end of input")

private partial def parseProgramAux (acc : Program) : ParserM Program := do
  ws
  if ← isEof then
    pure acc.reverse
  else
    let item ← parseItem
    parseProgramAux (item :: acc)

def parse (s : String) : Except ParseError Program :=
  match parseProgramAux [] (initState s) with
  | .ok (prog, _) => .ok prog
  | .error e => .error e

end Qdt.Frontend.Parser
