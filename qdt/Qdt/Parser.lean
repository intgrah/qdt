import Qdt.Syntax
import Qdt.Lexer
import Parser

namespace Qdt

open Parser

abbrev TokenStream := Parser.Stream.OfList Token
abbrev TokenParser := SimpleParser TokenStream Token

def tok (t : Token) : TokenParser Token :=
  withErrorMessage s!"expected {t}" <| token t

def pIdentTok : TokenParser String := do
  match ← anyToken with
  | Token.ident name => return name
  | t => throwUnexpectedWithMessage t s!"expected identifier"

def pBinderName : TokenParser Name := do
  match ← anyToken with
  | Token.underscore => return none
  | Token.ident name => return some name
  | t => throwUnexpectedWithMessage t s!"expected binder name"

mutual
  partial def pAtom : TokenParser Raw :=
    first [pFst, pSnd, pRefl, pAbsurd, pSorry, pVar, pType, pUnitTy, pEmpty, pIntTy, pIntLit, pPair, pUnitTerm, pAnnOrParens]

  partial def pVar : TokenParser Raw := Raw.ident <$> pIdentTok

  partial def pType : TokenParser Raw := tok Token.type *> pure Raw.u

  partial def pUnitTy : TokenParser Raw := tok Token.unit *> pure Raw.unit

  partial def pEmpty : TokenParser Raw := tok Token.empty *> pure Raw.empty

  partial def pIntTy : TokenParser Raw := tok Token.int *> pure Raw.int

  partial def pIntLit : TokenParser Raw := do
    match ← anyToken with
    | Token.intLit n => return Raw.intLit n
    | t => throwUnexpectedWithMessage t s!"expected integer literal"

  partial def pUnitTerm : TokenParser Raw :=
    tok Token.lparen *> tok Token.rparen *> pure Raw.unitTm

  partial def pPair : TokenParser Raw := do
    let _ ← tok Token.lparen
    let a ← pPreterm
    let _ ← tok Token.comma
    let b ← pPreterm
    let _ ← tok Token.rparen
    return Raw.pair a b

  partial def pFst : TokenParser Raw := do
    let _ ← tok Token.fst
    Raw.proj1 <$> pAtom

  partial def pSnd : TokenParser Raw := do
    let _ ← tok Token.snd
    Raw.proj2 <$> pAtom

  partial def pRefl : TokenParser Raw := do
    let _ ← tok Token.refl
    Raw.refl <$> pAtom

  partial def pAbsurd : TokenParser Raw := do
    let _ ← tok Token.absurd
    Raw.absurd <$> pAtom

  partial def pSorry : TokenParser Raw := tok Token.sorry *> pure Raw.sorry

  partial def pAnnOrParens : TokenParser Raw := do
    let _ ← tok Token.lparen
    let e ← pPreterm
    (do let _ ← tok Token.colon
        let ty ← pPreterm
        let _ ← tok Token.rparen
        return Raw.ann e ty)
    <|> (tok Token.rparen *> pure e)

  partial def pTypedBinderGroup : TokenParser (List Name × Raw) := do
    let _ ← tok Token.lparen
    let names ← takeMany1 pBinderName
    let _ ← tok Token.colon
    let ty ← pPreterm
    let _ ← tok Token.rparen
    return (names.toList, ty)

  partial def pParenBinderGroup : TokenParser (List (Name × Option Raw)) := do
    let _ ← tok Token.lparen
    let names ← takeMany1 pBinderName
    let tyOpt ← option? (tok Token.colon *> pPreterm)
    let _ ← tok Token.rparen
    return names.toList.map (·, tyOpt)

  partial def pLambda : TokenParser Raw := do
    let _ ← tok Token.fun
    let parenGroups ← takeMany pParenBinderGroup
    let parenBinders := parenGroups.toList.flatten
    let allBinders ←
      if parenBinders.isEmpty then do
        let names ← takeMany1 pBinderName
        let tyOpt ← option? (tok Token.colon *> pPreterm)
        pure (names.toList.map (·, tyOpt))
      else do
        let bareNames ← takeMany pBinderName
        pure (parenBinders ++ bareNames.toList.map (·, none))
    let _ ← tok Token.eqGt
    let body ← pPreterm
    return Raw.lam allBinders body

  partial def pLet : TokenParser Raw := do
    let _ ← tok Token.let
    let name ← pIdentTok
    let tyOpt ← option? (tok Token.colon *> pArrowLevel)
    let _ ← tok Token.colonEq
    let e ← pPreterm
    let _ ← tok Token.semicolon
    let body ← pPreterm
    return Raw.let name tyOpt e body

  partial def pPi : TokenParser Raw := do
    let (names, ty) ← pTypedBinderGroup
    let _ ← tok Token.arrow
    let b ← pPreterm
    return Raw.pi (names, ty) b

  partial def pSigma : TokenParser Raw := do
    let (names, ty) ← pTypedBinderGroup
    let _ ← tok Token.times
    let b ← pPreterm
    return Raw.sigma (names, ty) b

  partial def pApp : TokenParser Raw := do
    let head ← pAtom
    let args ← takeMany pAtom
    return args.foldl (fun f a => Raw.app f a) head

  partial def pAddLevel : TokenParser Raw := do
    let first ← pApp
    let rec go (acc : Raw) : TokenParser Raw :=
      (do let _ ← tok Token.plus; let b ← pApp; go (Raw.add acc b))
      <|> (do let _ ← tok Token.minus; let b ← pApp; go (Raw.sub acc b))
      <|> pure acc
    go first

  partial def pEqLevel : TokenParser Raw := do
    let a ← pAddLevel
    (do let _ ← tok Token.equal; let b ← pAddLevel; return Raw.eq a b)
    <|> pure a

  partial def pProdLevel : TokenParser Raw :=
    pSigma <|> do
      let a ← pEqLevel
      (do let _ ← tok Token.times; let b ← pProdLevel; return Raw.prod a b)
      <|> pure a

  partial def pArrowLevel : TokenParser Raw :=
    pPi <|> do
      let a ← pProdLevel
      (do let _ ← tok Token.arrow; let b ← pArrowLevel; return Raw.arrow a b)
      <|> pure a

  partial def pPreterm : TokenParser Raw :=
    first [pLambda, pLet, pPi, pSigma, pArrowLevel]

  partial def pDef : TokenParser RawDef := do
    let _ ← tok Token.def
    let name ← pIdentTok
    let binderGroups ← takeMany pTypedBinderGroup
    let binders : List (Name × Option Raw) :=
      binderGroups.toList.flatMap fun (names, ty) => names.map (·, some ty)
    let retTyOpt ← option? (tok Token.colon *> pArrowLevel)
    let _ ← tok Token.colonEq
    let body ← pPreterm
    let bodyWithAnn := match retTyOpt with
      | some ty => Raw.ann body ty
      | none => body
    let fullBody := if binders.isEmpty then bodyWithAnn else Raw.lam binders bodyWithAnn
    return (name, fullBody)
end

def pProgram : TokenParser RawProgram := do
  let defs ← takeMany pDef
  endOfInput
  return defs.toList

def parse (tokens : List Token) : Except String RawProgram :=
  match Parser.run pProgram (Parser.Stream.mkOfList tokens) with
  | .ok _ prog => .ok prog
  | .error _ e => .error s!"Parse error: {repr e}"

def parseString (s : String) : Except String RawProgram := do
  let tokens ← tokenize s
  parse tokens

end Qdt
