import Qdt.Frontend.Ast
import Qdt.Frontend.Cst

namespace Qdt.Frontend

open Lean (Name SyntaxNodeKind)

structure DesugarState where
  sourceMap : SourceMap
  cstPath : Path
  astPath : Path

abbrev DesugarM := StateM DesugarState

private def recordMapping : DesugarM Unit := do
  let st ← get
  set { st with sourceMap := st.sourceMap.insert st.cstPath.reverse st.astPath.reverse }

private def withCstChild {α : Type} (idx : Nat) (m : DesugarM α) : DesugarM α := do
  let st ← get
  set { st with cstPath := idx :: st.cstPath }
  let result ← m
  modify fun s => { s with cstPath := st.cstPath }
  return result

private def withAstChild {α : Type} (idx : Nat) (m : DesugarM α) : DesugarM α := do
  let st ← get
  set { st with astPath := idx :: st.astPath }
  let result ← m
  modify fun s => { s with astPath := st.astPath }
  return result

private def isTrivia (cst : Cst) : Bool :=
  match cst with
  | .token `ws _ => true
  | .token `comment _ => true
  | _ => false

private def filterTrivia (args : Array Cst) : Array Cst :=
  args.filter (!isTrivia ·)

private def childrenNoTrivia (cst : Cst) : Array Cst :=
  match cst with
  | .node _ args => filterTrivia args
  | _ => #[]

structure IndexedCst where
  idx : Nat
  cst : Cst

private def nonTriviaIndices (args : Array Cst) : Array IndexedCst := Id.run do
  let mut result : Array IndexedCst := #[]
  for h : i in [0:args.size] do
    let cst := args[i]
    if !isTrivia cst then
      result := result.push ⟨i, cst⟩
  return result

private def getIdentVal (cst : Cst) : Option String :=
  match cst with
  | .token `ident val => some val
  | _ => none

private def getNumVal (cst : Cst) : Option String :=
  match cst with
  | .token `num val => some val
  | _ => none

private def isAtom (s : String) (cst : Cst) : Bool :=
  match cst with
  | .token `atom val => val == s
  | _ => false

partial def desugarLevel (cst : Cst) : DesugarM Ast := do
  recordMapping
  match cst with
  | .token `num val =>
      match val.toNat? with
      | some n => return buildSucc n
      | none => return .missing
  | .node `Lean.Parser.Level.num args =>
      let nonTrivia := nonTriviaIndices args
      match nonTrivia[0]? with
      | some ic =>
          match getNumVal ic.cst with
          | some val =>
              match val.toNat? with
              | some n => return buildSucc n
              | none => return .missing
          | none => return .missing
      | none => return .missing
  | .node `Lean.Parser.Level.ident args =>
      let nonTrivia := nonTriviaIndices args
      match nonTrivia[0]? with
      | some ic =>
          match getIdentVal ic.cst with
          | some val =>
              withCstChild ic.idx do
                recordMapping
                return .node `Level.name #[.ident val.toName]
          | none => return .missing
      | none => return .missing
  | .node `Lean.Parser.Level.max args =>
      let nonTrivia := nonTriviaIndices args
      let levelArgs := nonTrivia.filter fun ic =>
        match ic.cst with
        | .node `null _ => false
        | .token `atom "max" => false
        | .token `ident "max" => false
        | _ => true
      if h : levelArgs.size ≥ 2 then
        let first ← withCstChild levelArgs[0].idx <| withAstChild 0 <| desugarLevel levelArgs[0].cst
        let second ← withCstChild levelArgs[1].idx <| withAstChild 1 <| desugarLevel levelArgs[1].cst
        let rest ← levelArgs.toList.drop 2 |>.mapIdxM fun i ic =>
          withCstChild ic.idx <| withAstChild (i + 2) <| desugarLevel ic.cst
        return rest.foldl (fun acc u => Ast.node `Level.max #[acc, u]) (.node `Level.max #[first, second])
      else
        return .missing
  | .node `Lean.Parser.Level.addLit args =>
      let nonTrivia := nonTriviaIndices args
      match nonTrivia[0]?, nonTrivia[2]? with
      | some baseIc, some numIc =>
          let baseLevel ← withCstChild baseIc.idx <| withAstChild 0 <| desugarLevel baseIc.cst
          match getNumVal numIc.cst with
          | some val =>
              match val.toNat? with
              | some n => return addSucc n baseLevel
              | none => return .missing
          | none => return .missing
      | _, _ => return .missing
  | .node `Lean.Parser.Level.paren args =>
      let nonTrivia := nonTriviaIndices args
      match nonTrivia[1]? with
      | some ic => withCstChild ic.idx <| desugarLevel ic.cst
      | none => return .missing
  | _ => return .missing
where
  buildSucc (n : Nat) : Ast :=
    match n with
    | 0 => .node `Level.zero #[]
    | n + 1 => .node `Level.succ #[buildSucc n]
  addSucc (n : Nat) (base : Ast) : Ast :=
    match n with
    | 0 => base
    | n + 1 => .node `Level.succ #[addSucc n base]

mutual

partial def desugarTerm (cst : Cst) : DesugarM Ast := do
  recordMapping
  match cst with
  | .token `ident val =>
      return .node `Term.ident #[.ident val.toName, .node `null #[]]
  | .token `num val =>
      match val.toNat? with
      | some n => return buildNatLit n
      | none => return .missing
  | .token _ _ => return .missing
  | .node kind args =>
      let nonTrivia := nonTriviaIndices args
      match kind with
      | `Lean.Parser.Term.app =>
          match nonTrivia[0]?, nonTrivia[1]? with
          | some fnIc, some argIc =>
              let fn ← withCstChild fnIc.idx <| withAstChild 0 <| desugarTerm fnIc.cst
              let arg ← withCstChild argIc.idx <| withAstChild 1 <| desugarTerm argIc.cst
              return .node `Term.app #[fn, arg]
          | _, _ => return .missing

      | `Lean.Parser.Term.fun =>
          desugarFun nonTrivia

      | `Lean.Parser.Term.arrow =>
          desugarArrowRight cst

      | `Lean.Parser.Term.depArrow =>
          match nonTrivia[0]?, nonTrivia[2]? with
          | some binderIc, some bodyIc =>
              desugarDepArrow binderIc bodyIc
          | _, _ => return .missing

      | `Lean.Parser.Term.type =>
          recordMapping
          let levelArgs := nonTrivia.filter fun ic =>
            match ic.cst with
            | .token `atom "Type" => false
            | _ => true
          match levelArgs[0]? with
          | some ic =>
              let level ← withCstChild ic.idx <| withAstChild 0 <| desugarLevel ic.cst
              return .node `Term.u #[level]
          | none =>
              return .node `Term.u #[.node `Level.zero #[]]

      | `Lean.Parser.Term.paren =>
          match nonTrivia[1]? with
          | some ic => withCstChild ic.idx <| desugarTerm ic.cst
          | none => return .missing

      | `Lean.Parser.Term.typeAscription =>
          match nonTrivia[1]?, nonTrivia[3]? with
          | some eIc, some tyIc =>
              let e ← withCstChild eIc.idx <| withAstChild 0 <| desugarTerm eIc.cst
              let ty ← withCstChild tyIc.idx <| withAstChild 1 <| desugarTerm tyIc.cst
              return .node `Term.ann #[e, ty]
          | _, _ => return .missing

      | `Lean.Parser.Term.let =>
          desugarLet nonTrivia

      | `Lean.Parser.Term.sorry =>
          return .node `Term.sorry #[]

      | `Lean.Parser.Term.explicitUniv =>
          match nonTrivia[0]?, nonTrivia[1]? with
          | some identIc, some univIc =>
              match getIdentVal identIc.cst with
              | some val =>
                  withCstChild identIc.idx do
                    recordMapping
                    let levels ← desugarUnivArgs univIc.cst
                    return .node `Term.ident #[.ident val.toName, .node `null levels.toArray]
              | none => return .missing
          | _, _ => return .missing

      | `Lean.Parser.Term.ident =>
          match nonTrivia[0]? with
          | some ic =>
              match getIdentVal ic.cst with
              | some val =>
                  withCstChild ic.idx do
                    recordMapping
                    return .node `Term.ident #[.ident val.toName, .node `null #[]]
              | none => return .missing
          | none => return .missing

      | `Lean.Parser.Term.unit =>
          return .node `Term.ident #[.ident `Unit.unit, .node `null #[]]

      | `Lean.Parser.Term.hole =>
          return .missing

      | `Lean.Parser.Term.num =>
          match nonTrivia[0]? with
          | some ic =>
              match getNumVal ic.cst with
              | some val =>
                  match val.toNat? with
                  | some n => return buildNatLit n
                  | none => return .missing
              | none => return .missing
          | none => return .missing

      | `«term_=_» =>
          match nonTrivia[0]?, nonTrivia[2]? with
          | some aIc, some bIc =>
              let a ← withCstChild aIc.idx <| withAstChild 0 <| desugarTerm aIc.cst
              let b ← withCstChild bIc.idx <| withAstChild 1 <| desugarTerm bIc.cst
              return .node `Term.eq #[a, b]
          | _, _ => return .missing

      | `«term_+_» =>
          match nonTrivia[0]?, nonTrivia[2]? with
          | some aIc, some bIc =>
              let a ← withCstChild aIc.idx <| desugarTerm aIc.cst
              let b ← withCstChild bIc.idx <| desugarTerm bIc.cst
              return .node `Term.app #[.node `Term.app #[.node `Term.ident #[.ident `Nat.add, .node `null #[]], a], b]
          | _, _ => return .missing

      | _ =>
          match nonTrivia[0]? with
          | some ic => withCstChild ic.idx <| desugarTerm ic.cst
          | none => return .missing
where
  buildNatLit (n : Nat) : Ast :=
    match n with
    | 0 => .node `Term.ident #[.ident `Nat.zero, .node `null #[]]
    | n + 1 => .node `Term.app #[.node `Term.ident #[.ident `Nat.succ, .node `null #[]], buildNatLit n]

  desugarArrowRight (cst : Cst) : DesugarM Ast := do
    match cst with
    | .node `Lean.Parser.Term.arrow args =>
        let nonTrivia := nonTriviaIndices args
        match nonTrivia[0]?, nonTrivia[2]? with
        | some lhsIc, some rhsIc =>
            let dom ← withCstChild lhsIc.idx <| withAstChild 0 <| withAstChild 1 <| desugarTerm lhsIc.cst
            let binder := Ast.node `Binder.typed #[.ident Name.anonymous, dom]
            let cod ← withCstChild rhsIc.idx <| withAstChild 1 <| desugarArrowRight rhsIc.cst
            return .node `Term.pi #[binder, cod]
        | _, _ => desugarTerm cst
    | _ => desugarTerm cst

  desugarUnivArgs (cst : Cst) : DesugarM (List Ast) := do
    match cst with
    | .node _ args =>
        let nonTrivia := nonTriviaIndices args
        let levelArgs := nonTrivia.filter fun ic => !isAtom "." ic.cst && !isAtom "{" ic.cst && !isAtom "}" ic.cst && !isAtom "," ic.cst
        levelArgs.toList.mapM fun ic =>
          withCstChild ic.idx <| desugarLevel ic.cst
    | _ => return []

  desugarFun (nonTrivia : Array IndexedCst) : DesugarM Ast := do
    let binderArgs := nonTrivia.toList.drop 1 |>.filter fun ic =>
      match ic.cst with
      | .token `atom _ => false
      | _ => true
    let (binderParts, bodyPart) :=
      match binderArgs.reverse with
      | body :: rest => (rest.reverse, some body)
      | [] => ([], none)
    match bodyPart with
    | some bodyIc => desugarFunGo binderParts bodyIc
    | none => return .missing

  desugarFunGo (binderParts : List IndexedCst) (bodyIc : IndexedCst) : DesugarM Ast := do
    match binderParts with
    | [] =>
        withCstChild bodyIc.idx <| desugarTerm bodyIc.cst
    | head :: tail =>
        withCstChild head.idx <| desugarFunBinderGo head.cst tail bodyIc

  desugarFunBinderGo (cst : Cst) (tail : List IndexedCst) (bodyIc : IndexedCst) : DesugarM Ast := do
    match cst with
    | .token `ident val =>
        withAstChild 0 <| withAstChild 0 recordMapping
        let binder := Ast.node `Binder.untyped #[.ident val.toName]
        let rest ← withAstChild 1 <| desugarFunGo tail bodyIc
        return .node `Term.lam #[binder, rest]
    | .node `Lean.Parser.Term.hole _ =>
        withAstChild 0 <| withAstChild 0 recordMapping
        let binder := Ast.node `Binder.untyped #[.ident Name.anonymous]
        let rest ← withAstChild 1 <| desugarFunGo tail bodyIc
        return .node `Term.lam #[binder, rest]
    | .node `Lean.Parser.Term.explicitBinder args =>
        let nonTrivia := nonTriviaIndices args
        let nameIndices := nonTrivia.filter fun ic =>
          match ic.cst with
          | .token `ident _ => true
          | .node `Lean.Parser.Term.hole _ => true
          | _ => false
        let typeIdx := nonTrivia.toList.findIdx? fun ic => isAtom ":" ic.cst
        let typeIc? := match typeIdx with
          | some colonPos => nonTrivia[colonPos + 1]?
          | none => none
        desugarFunTypedBinderGo nameIndices.toList typeIc? tail bodyIc none
    | _ => desugarFunGo tail bodyIc

  desugarFunTypedBinderGo (names : List IndexedCst) (typeIc? : Option IndexedCst) (tail : List IndexedCst) (bodyIc : IndexedCst) (tyAst? : Option Ast) : DesugarM Ast := do
    match names with
    | [] => desugarFunGo tail bodyIc
    | [single] =>
        let name := match getIdentVal single.cst with
          | some v => v.toName
          | none => Name.anonymous
        withCstChild single.idx <| withAstChild 0 <| withAstChild 0 recordMapping
        let ty ← match tyAst? with
          | some ty => pure ty
          | none => match typeIc? with
              | some tyIc => withCstChild tyIc.idx <| withAstChild 0 <| withAstChild 1 <| desugarTerm tyIc.cst
              | none => pure .missing
        let binder := Ast.node `Binder.typed #[.ident name, ty]
        let rest ← withAstChild 1 <| desugarFunGo tail bodyIc
        return .node `Term.lam #[binder, rest]
    | head :: remaining =>
        let name := match getIdentVal head.cst with
          | some v => v.toName
          | none => Name.anonymous
        withCstChild head.idx <| withAstChild 0 <| withAstChild 0 recordMapping
        let ty ← match tyAst? with
          | some ty => pure ty
          | none => match typeIc? with
              | some tyIc => withCstChild tyIc.idx <| withAstChild 0 <| withAstChild 1 <| desugarTerm tyIc.cst
              | none => pure .missing
        let binder := Ast.node `Binder.typed #[.ident name, ty]
        let rest ← withAstChild 1 <| desugarFunTypedBinderGo remaining typeIc? tail bodyIc (some ty)
        return .node `Term.lam #[binder, rest]

  desugarDepArrow (binderIc : IndexedCst) (bodyIc : IndexedCst) : DesugarM Ast := do
    let args := childrenNoTrivia binderIc.cst
    let nonTrivia := nonTriviaIndices args
    let nameIndices := nonTrivia.filter fun ic =>
      match ic.cst with
      | .token `ident _ => true
      | .node `Lean.Parser.Term.hole _ => true
      | _ => false
    let typeIdx := nonTrivia.toList.findIdx? fun ic => isAtom ":" ic.cst
    let typeIc? := match typeIdx with
      | some colonPos => nonTrivia[colonPos + 1]?
      | none => none
    withCstChild binderIc.idx <| desugarDepArrowGo nameIndices.toList typeIc? bodyIc none

  desugarDepArrowGo (names : List IndexedCst) (typeIc? : Option IndexedCst) (bodyIc : IndexedCst) (tyAst? : Option Ast) : DesugarM Ast := do
    match names with
    | [] => withCstChild bodyIc.idx <| desugarTerm bodyIc.cst
    | [single] =>
        let name := match getIdentVal single.cst with
          | some v => v.toName
          | none => Name.anonymous
        withCstChild single.idx <| withAstChild 0 <| withAstChild 0 recordMapping
        let ty ← match tyAst? with
          | some ty => pure ty
          | none => match typeIc? with
              | some tyIc => withCstChild tyIc.idx <| withAstChild 0 <| withAstChild 1 <| desugarTerm tyIc.cst
              | none => pure .missing
        let binder := Ast.node `Binder.typed #[.ident name, ty]
        let body ← withCstChild bodyIc.idx <| withAstChild 1 <| desugarTerm bodyIc.cst
        return .node `Term.pi #[binder, body]
    | head :: tail =>
        let name := match getIdentVal head.cst with
          | some v => v.toName
          | none => Name.anonymous
        withCstChild head.idx <| withAstChild 0 <| withAstChild 0 recordMapping
        let ty ← match tyAst? with
          | some ty => pure ty
          | none => match typeIc? with
              | some tyIc => withCstChild tyIc.idx <| withAstChild 0 <| withAstChild 1 <| desugarTerm tyIc.cst
              | none => pure .missing
        let binder := Ast.node `Binder.typed #[.ident name, ty]
        let rest ← withAstChild 1 <| desugarDepArrowGo tail typeIc? bodyIc (some ty)
        return .node `Term.pi #[binder, rest]

  desugarLet (nonTrivia : Array IndexedCst) : DesugarM Ast := do
    match nonTrivia[1]? with
    | some nameIc =>
        match getIdentVal nameIc.cst with
        | some nameVal =>
            let colonIdx := nonTrivia.toList.findIdx? fun ic => isAtom ":" ic.cst
            let assignIdx := nonTrivia.toList.findIdx? fun ic => isAtom ":=" ic.cst
            let semiIdx := nonTrivia.toList.findIdx? fun ic => isAtom ";" ic.cst
            withCstChild nameIc.idx do
              recordMapping
              match assignIdx, semiIdx with
              | some aIdx, some sIdx =>
                  let hasType := match colonIdx with
                    | some c => decide (c < aIdx)
                    | none => false
                  if hasType then
                    match nonTrivia[colonIdx.get! + 1]?, nonTrivia[aIdx + 1]?, nonTrivia[sIdx + 1]? with
                    | some tyIc, some rhsIc, some bodyIc =>
                        let ty ← withCstChild tyIc.idx <| withAstChild 1 <| desugarTerm tyIc.cst
                        let rhs ← withCstChild rhsIc.idx <| withAstChild 2 <| desugarTerm rhsIc.cst
                        let body ← withCstChild bodyIc.idx <| withAstChild 3 <| desugarTerm bodyIc.cst
                        return .node `Term.letE #[.ident nameVal.toName, ty, rhs, body]
                    | _, _, _ => return .missing
                  else
                    match nonTrivia[aIdx + 1]?, nonTrivia[sIdx + 1]? with
                    | some rhsIc, some bodyIc =>
                        let rhs ← withCstChild rhsIc.idx <| withAstChild 2 <| desugarTerm rhsIc.cst
                        let body ← withCstChild bodyIc.idx <| withAstChild 3 <| desugarTerm bodyIc.cst
                        return .node `Term.letE #[.ident nameVal.toName, .missing, rhs, body]
                    | _, _ => return .missing
              | _, _ => return .missing
        | none => return .missing
    | none => return .missing

partial def desugarBinder (cst : Cst) : DesugarM (List Ast) := do
  match cst with
  | .token `ident val =>
      recordMapping
      return [.node `Binder.untyped #[.ident val.toName]]
  | .node `Lean.Parser.Term.hole _ =>
      return [.node `Binder.untyped #[.ident Name.anonymous]]
  | .node `Lean.Parser.Term.explicitBinder args =>
      let binders ← desugarTypedBinderGroupCmd args
      return binders.map (·.1)
  | _ => return []

partial def desugarTypedBinderGroupCmd (args : Array Cst) (binderStartIdx : Nat := 0) : DesugarM (List (Ast × Bool)) := do
  let nonTrivia := nonTriviaIndices args
  let nameIndices := nonTrivia.filter fun ic =>
    match ic.cst with
    | .token `ident _ => true
    | .node `Lean.Parser.Term.hole _ => true
    | _ => false
  let typeIdx := nonTrivia.toList.findIdx? fun ic => isAtom ":" ic.cst
  let typeIc? := match typeIdx with
    | some colonPos => nonTrivia[colonPos + 1]?
    | none => none
  let mut tyAst : Ast := .missing
  let mut results : List (Ast × Bool) := []
  for h : i in [:nameIndices.size] do
    let ic := nameIndices[i]
    let name := match getIdentVal ic.cst with
      | some v => v.toName
      | none => Name.anonymous
    let isFirst := i == 0
    withCstChild ic.idx <| withAstChild (binderStartIdx + i) <| withAstChild 0 do
      recordMapping
    let ty ← if isFirst then
      match typeIc? with
      | some tyIc => withCstChild tyIc.idx <| withAstChild (binderStartIdx + i) <| withAstChild 1 <| desugarTerm tyIc.cst
      | none => pure .missing
    else
      pure tyAst
    if isFirst then
      tyAst := ty
    results := results ++ [(.node `Binder.typed #[.ident name, ty], isFirst)]
  return results

end

def desugarDeclId (cst : Cst) : DesugarM (Name × List Name) := do
  match cst with
  | .node _ args =>
      let nonTrivia := nonTriviaIndices args
      let name := match nonTrivia[0]? with
        | some ic => (getIdentVal ic.cst).map (·.toName) |>.getD Name.anonymous
        | none => Name.anonymous
      match nonTrivia[0]? with
      | some ic => withCstChild ic.idx recordMapping
      | none => pure ()
      let univParams := match nonTrivia[1]? with
        | some ic =>
            match ic.cst with
            | .node _ univArgs =>
                let inner := nonTriviaIndices univArgs
                inner.toList.filterMap fun ic2 => (getIdentVal ic2.cst).map (·.toName)
            | _ => []
        | none => []
      return (name, univParams)
  | _ => return (Name.anonymous, [])

def desugarOptDeclSig (cst : Cst) (paramsAstIdx : Nat) (retTypeAstIdx : Option Nat := none) : DesugarM (List Ast × Option Ast) := do
  match cst with
  | .node _ args =>
      let nonTrivia := nonTriviaIndices args
      let mut binders : List Ast := []
      let mut binderIdx : Nat := 0
      let mut tyOpt : Option Ast := none
      for ic in nonTrivia do
        match ic.cst with
        | .node `Lean.Parser.Term.explicitBinder innerArgs =>
            let bs ← withCstChild ic.idx <| withAstChild paramsAstIdx <| desugarTypedBinderGroupCmd innerArgs binderIdx
            for (b, _) in bs do
              binders := binders ++ [b]
              binderIdx := binderIdx + 1
        | .token `atom ":" =>
            let colonPos := nonTrivia.toList.findIdx? fun ic2 => ic2.idx == ic.idx
            match colonPos.bind (fun p => nonTrivia[p + 1]?) with
            | some tyIc =>
                let desugar := withCstChild tyIc.idx <| desugarTerm tyIc.cst
                tyOpt ← some <$> match retTypeAstIdx with
                  | some idx => withAstChild idx desugar
                  | none => desugar
            | none => pure ()
            break
        | _ => pure ()
      return (binders, tyOpt)
  | _ => return ([], none)

def desugarDeclSig (cst : Cst) (paramsAstIdx : Nat) (retTypeAstIdx : Option Nat := none) : DesugarM (List Ast × Ast) := do
  let (binders, tyOpt) ← desugarOptDeclSig cst paramsAstIdx retTypeAstIdx
  return (binders, tyOpt.getD .missing)

def desugarDeclValSimple (cst : Cst) : DesugarM Ast := do
  match cst with
  | .node _ args =>
      let nonTrivia := nonTriviaIndices args
      match nonTrivia[1]? with
      | some ic => withCstChild ic.idx <| desugarTerm ic.cst
      | none => return .missing
  | _ => return .missing

def desugarDefinition (cst : Cst) : DesugarM Ast := do
  match cst with
  | .node _ args =>
      let nonTrivia := nonTriviaIndices args
      match nonTrivia[1]?, nonTrivia[2]?, nonTrivia[3]? with
      | some declIdIc, some optSigIc, some declValIc =>
          let (name, univParams) ← withCstChild declIdIc.idx <| withAstChild 0 <| desugarDeclId declIdIc.cst
          let (params, tyOpt) ← withCstChild optSigIc.idx <| desugarOptDeclSig optSigIc.cst 2 (some 3)
          let body ← withCstChild declValIc.idx <| withAstChild 4 <| desugarDeclValSimple declValIc.cst
          let univParamsAst := Ast.node `null (univParams.map Ast.ident).toArray
          let paramsAst := Ast.node `null params.toArray
          let tyAst := tyOpt.getD .missing
          return .node `Command.definition #[.ident name, univParamsAst, paramsAst, tyAst, body]
      | _, _, _ => return .missing
  | _ => return .missing

def desugarExample (cst : Cst) : DesugarM Ast := do
  match cst with
  | .node _ args =>
      let nonTrivia := nonTriviaIndices args
      match nonTrivia[1]?, nonTrivia[2]? with
      | some optSigIc, some declValIc =>
          let (params, tyOpt) ← withCstChild optSigIc.idx <| desugarOptDeclSig optSigIc.cst 0 (some 1)
          let body ← withCstChild declValIc.idx <| withAstChild 2 <| desugarDeclValSimple declValIc.cst
          let paramsAst := Ast.node `null params.toArray
          let tyAst := tyOpt.getD .missing
          return .node `Command.example #[paramsAst, tyAst, body]
      | _, _ => return .missing
  | _ => return .missing

def desugarAxiom (cst : Cst) : DesugarM Ast := do
  match cst with
  | .node _ args =>
      let nonTrivia := nonTriviaIndices args
      match nonTrivia[1]?, nonTrivia[2]? with
      | some declIdIc, some declSigIc =>
          let (name, univParams) ← withCstChild declIdIc.idx <| withAstChild 0 <| desugarDeclId declIdIc.cst
          let (params, ty) ← withCstChild declSigIc.idx <| desugarDeclSig declSigIc.cst 2 (some 3)
          let univParamsAst := Ast.node `null (univParams.map Ast.ident).toArray
          let paramsAst := Ast.node `null params.toArray
          return .node `Command.axiom #[.ident name, univParamsAst, paramsAst, ty]
      | _, _ => return .missing
  | _ => return .missing

def desugarCtor (cst : Cst) : DesugarM Ast := do
  match cst with
  | .node _ args =>
      let nonTrivia := nonTriviaIndices args
      match nonTrivia[1]?, nonTrivia[2]? with
      | some nameIc, some optSigIc =>
          match getIdentVal nameIc.cst with
          | some nameVal =>
              withCstChild nameIc.idx recordMapping
              let (fields, tyOpt) ← withCstChild optSigIc.idx <| desugarOptDeclSig optSigIc.cst 1 (some 2)
              let fieldsAst := Ast.node `null fields.toArray
              let tyAst := tyOpt.getD .missing
              return .node `Constructor #[.ident nameVal.toName, fieldsAst, tyAst]
          | none => return .missing
      | _, _ => return .missing
  | _ => return .missing

def desugarInductive (cst : Cst) : DesugarM Ast := do
  match cst with
  | .node _ args =>
      let nonTrivia := nonTriviaIndices args
      let nonTrivia := nonTrivia.filter fun ic => !isAtom "where" ic.cst
      match nonTrivia[1]?, nonTrivia[2]? with
      | some declIdIc, some optSigIc =>
          let (name, univParams) ← withCstChild declIdIc.idx <| withAstChild 0 <| desugarDeclId declIdIc.cst
          let (params, tyOpt) ← withCstChild optSigIc.idx <| desugarOptDeclSig optSigIc.cst 2 (some 3)
          let ctorArgs := nonTrivia.toList.drop 3
          let ctors ← ctorArgs.mapIdxM fun i ic =>
            withCstChild ic.idx <| withAstChild (4 + i) <| desugarCtor ic.cst
          let univParamsAst := Ast.node `null (univParams.map Ast.ident).toArray
          let paramsAst := Ast.node `null params.toArray
          let tyAst := tyOpt.getD .missing
          let ctorsAst := Ast.node `null ctors.toArray
          return .node `Command.inductive #[.ident name, univParamsAst, paramsAst, tyAst, ctorsAst]
      | _, _ => return .missing
  | _ => return .missing

def desugarStructField (cst : Cst) : DesugarM Ast := do
  match cst with
  | .node _ args =>
      let nonTrivia := nonTriviaIndices args
      match nonTrivia[1]?, nonTrivia[2]? with
      | some nameIc, some optSigIc =>
          match getIdentVal nameIc.cst with
          | some nameVal =>
              withCstChild nameIc.idx recordMapping
              let (params, tyOpt) ← withCstChild optSigIc.idx <| desugarOptDeclSig optSigIc.cst 1 (some 2)
              let ty := tyOpt.getD .missing
              let paramsAst := Ast.node `null params.toArray
              return .node `StructureField #[.ident nameVal.toName, paramsAst, ty]
          | none => return .missing
      | _, _ => return .missing
  | _ => return .missing

def desugarStructure (cst : Cst) : DesugarM Ast := do
  match cst with
  | .node _ args =>
      let nonTrivia := nonTriviaIndices args
      let nonTrivia := nonTrivia.filter fun ic => !isAtom "where" ic.cst
      match nonTrivia[1]?, nonTrivia[2]? with
      | some declIdIc, some optSigIc =>
          let (name, univParams) ← withCstChild declIdIc.idx <| withAstChild 0 <| desugarDeclId declIdIc.cst
          let (params, tyOpt) ← withCstChild optSigIc.idx <| desugarOptDeclSig optSigIc.cst 2 (some 3)
          let fieldArgs := nonTrivia.toList.drop 3
          let fields ← fieldArgs.mapIdxM fun i ic =>
            withCstChild ic.idx <| withAstChild (4 + i) <| desugarStructField ic.cst
          let univParamsAst := Ast.node `null (univParams.map Ast.ident).toArray
          let paramsAst := Ast.node `null params.toArray
          let tyAst := tyOpt.getD .missing
          let fieldsAst := Ast.node `null fields.toArray
          return .node `Command.structure #[.ident name, univParamsAst, paramsAst, tyAst, fieldsAst]
      | _, _ => return .missing
  | _ => return .missing

def desugarImport (cst : Cst) : DesugarM Ast := do
  recordMapping
  match cst with
  | .node _ args =>
      let nonTrivia := nonTriviaIndices args
      match nonTrivia[1]? with
      | some ic =>
          match getIdentVal ic.cst with
          | some nameVal =>
              withCstChild ic.idx recordMapping
              return .node `Command.import #[.ident nameVal.toName]
          | none => return .missing
      | none => return .missing
  | _ => return .missing

private def matchKind (kind : SyntaxNodeKind) (name : String) : Bool :=
  kind == name.toName || kind.toString == name

partial def desugarCommand (cst : Cst) : DesugarM Ast := do
  recordMapping
  match cst with
  | .node kind args =>
      if matchKind kind "Lean.Parser.Command.declaration" then
        let nonTrivia := nonTriviaIndices args
        if h : nonTrivia.size ≥ 2 then
          desugarCommand nonTrivia[1].cst
        else
          return .missing
      else if matchKind kind "Lean.Parser.Command.definition" then desugarDefinition cst
      else if matchKind kind "Lean.Parser.Command.axiom" then desugarAxiom cst
      else if matchKind kind "Lean.Parser.Command.inductive" then desugarInductive cst
      else if matchKind kind "Lean.Parser.Command.structure" then desugarStructure cst
      else if matchKind kind "Lean.Parser.Command.example" then desugarExample cst
      else if matchKind kind "Lean.Parser.Command.import" then desugarImport cst
      else return .missing
  | _ => return .missing

def desugarProgram (module : Cst) : (Array Ast × SourceMap) :=
  let action : DesugarM (Array Ast) := do
    match module with
    | .node kind args =>
        if matchKind kind "Lean.Parser.Module" then
          let nonTrivia := nonTriviaIndices args
          let result ← nonTrivia.toList.mapIdxM fun i ic =>
            withCstChild ic.idx <| withAstChild i <| desugarCommand ic.cst
          return result.toArray
        else
          return #[]
    | _ => return #[]
  let init : DesugarState := { sourceMap := ⟨∅, ∅⟩, cstPath := [], astPath := [] }
  let (prog, st) := action.run init
  (prog, st.sourceMap)

end Qdt.Frontend
