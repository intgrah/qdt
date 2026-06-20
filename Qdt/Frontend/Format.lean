module

public import Qdt.Frontend.Cst
public import Lean.Data.Format

@[expose] public section

namespace Qdt.Frontend.Format

open Lean (Name SyntaxNodeKind Format)
open Std.Format (text line nest group fill joinSep)

namespace Prec
def min   : Nat := 0
def arrow : Nat := 25
def eq    : Nat := 50
def add   : Nat := 65
def app   : Nat := 1024
end Prec

def parensIf (cond : Bool) (f : Format) : Format :=
  if cond then "(" ++ f ++ ")" else f

def isTrivia : Cst → Bool
  | .token `ws _      => true
  | .token `comment _ => true
  | _                 => false

def isWs : Cst → Bool
  | .token `ws _ => true
  | _            => false

def isAtom (s : String) : Cst → Bool
  | .token `atom v => v == s
  | _              => false

def getIdent? : Cst → Option String
  | .token `ident v => some v
  | _               => none

def childrenOf : Cst → Array Cst
  | .node _ cs => cs
  | _          => #[]

def nonTrivia (args : Array Cst) : Array Cst :=
  args.filter (fun c => !isTrivia c)

structure Tagged where
  cst : Cst
  leading : Array String
  trailing : Array String

def tagChildren (args : Array Cst) : Array Tagged := Id.run do
  let mut out : Array Tagged := #[]
  let mut sawNewline : Bool := true
  let mut pendingTrailing : Array String := #[]
  let mut pendingLeading  : Array String := #[]
  for c in args do
    match c with
    | .token `ws v =>
        if v.contains '\n' then
          if !pendingTrailing.isEmpty then
            if out.size > 0 then
              let idx := out.size - 1
              out := out.modify idx fun t => { t with trailing := t.trailing ++ pendingTrailing }
            pendingTrailing := #[]
          sawNewline := true
    | .token `comment v =>
        if sawNewline then
          pendingLeading := pendingLeading.push v
        else
          pendingTrailing := pendingTrailing.push v
    | other =>
        if isTrivia other then continue
        if !pendingTrailing.isEmpty then
          if out.size > 0 then
            let idx := out.size - 1
            out := out.modify idx fun t => { t with trailing := t.trailing ++ pendingTrailing }
          pendingTrailing := #[]
        out := out.push { cst := other, leading := pendingLeading, trailing := #[] }
        pendingLeading := #[]
        sawNewline := false
  if !pendingTrailing.isEmpty || !pendingLeading.isEmpty then
    if out.size > 0 then
      let idx := out.size - 1
      out := out.modify idx fun t =>
        { t with trailing := t.trailing ++ pendingTrailing ++ pendingLeading }
  return out

def renderComment (s : String) : Format :=
  text s.trimAsciiEnd.toString

def withLeading (leading : Array String) (f : Format) : Format :=
  if leading.isEmpty then f
  else
    leading.foldr (fun c acc => renderComment c ++ line ++ acc) f

def withTrailing (trailing : Array String) (f : Format) : Format :=
  if trailing.isEmpty then f
  else
    let suffix := trailing.foldl (fun acc c => acc ++ " " ++ renderComment c) Format.nil
    f ++ suffix

def flatten (f : Format) : Format :=
  text (Format.pretty f 999999)

partial def collectAppChain (cst : Cst) : Cst × Array Cst :=
  go cst #[]
where
  go (cst : Cst) (acc : Array Cst) : Cst × Array Cst :=
    match cst with
    | .node `Lean.Parser.Term.app args =>
        let nt := nonTrivia args
        match nt[0]?, nt[1]? with
        | some f, some a => go f (#[a] ++ acc)
        | _, _ => (cst, acc)
    | _ => (cst, acc)

mutual

partial def fmtTerm (prec : Nat) (cst : Cst) : Format :=
  match cst with
  | .token `ident v => text v
  | .token `num v   => text v
  | .token `atom "_" => "_"
  | .token _ _      => Format.nil
  | .node k args    =>
      match k with
      | `Lean.Parser.Term.ident =>
          match (nonTrivia args)[0]? with
          | some c => fmtTerm prec c
          | none   => Format.nil
      | `Lean.Parser.Term.num =>
          match (nonTrivia args)[0]? with
          | some c => fmtTerm prec c
          | none   => Format.nil
      | `Lean.Parser.Term.hole => "_"
      | `Lean.Parser.Term.sorry => "sorry"
      | `Lean.Parser.Term.unit => "()"
      | `Lean.Parser.Term.type =>
          let nt := nonTrivia args
          match nt[1]? with
          | some lvl =>
              parensIf (prec > Prec.app) <|
                "Type " ++ fmtLevel (Prec.app + 1) lvl
          | none     => "Type"
      | `Lean.Parser.Term.paren =>
          let nt := nonTrivia args
          match nt[1]? with
          | some inner => fmtTerm prec inner
          | none       => Format.nil
      | `Lean.Parser.Term.typeAscription =>
          let nt := nonTrivia args
          match nt[1]?, nt[3]? with
          | some e, some ty =>
              parensIf (prec > Prec.min) <|
                group (fmtTerm Prec.min e ++ " :"
                        ++ nest 2 (line ++ fmtTerm Prec.min ty))
          | _, _ => Format.nil
      | `Lean.Parser.Term.app =>
          let (head, chainArgs) := collectAppChain (.node k args)
          if chainArgs.isEmpty then fmtTerm prec head
          else
            let body := chainArgs.foldl
              (fun acc a => acc ++ line ++ fmtTerm (Prec.app + 1) a)
              Format.nil
            parensIf (prec > Prec.app) <|
              group (fmtTerm Prec.app head ++ nest 2 body)
      | `Lean.Parser.Term.explicitUniv =>
          let nt := nonTrivia args
          match nt[0]?, nt[1]? with
          | some ident, some univ =>
              fmtTerm prec ident ++ fmtUnivArgs univ
          | _, _ => Format.nil
      | `Lean.Parser.Term.arrow =>
          let nt := nonTrivia args
          match nt[0]?, nt[2]? with
          | some l, some r =>
              parensIf (prec > Prec.arrow) <|
                group (fmtTerm (Prec.arrow + 1) l ++ " →"
                        ++ line ++ fmtTerm Prec.arrow r)
          | _, _ => Format.nil
      | `Lean.Parser.Term.depArrow =>
          let nt := nonTrivia args
          match nt[0]?, nt[2]? with
          | some binder, some r =>
              parensIf (prec > Prec.arrow) <|
                group (fmtBinderGroup binder ++ " →"
                        ++ line ++ fmtTerm Prec.arrow r)
          | _, _ => Format.nil
      | `Lean.Parser.Term.explicit =>
          let nt := nonTrivia args
          match nt[1]? with
          | some ident => "@" ++ fmtTerm Prec.app ident
          | none       => Format.nil
      | `Lean.Parser.Term.fun =>
          let nt := nonTrivia args
          if h : nt.size >= 3 then
            let body := nt[nt.size - 1]
            let region := (nt.extract 1 (nt.size - 1)).filter
              (fun c => !isAtom "=>" c && !isAtom "⇒" c)
            let binderDoc :=
              match region.toList.findIdx? (isAtom ":") with
              | some ci =>
                  let names := region.extract 0 ci
                  let tyF := match region[ci + 1]? with
                    | some tyC => flatten (fmtTerm Prec.min tyC)
                    | none     => Format.nil
                  joinSep (names.toList.map fmtBinder) " " ++ " : " ++ tyF
              | none =>
                  match region[0]? with
                  | some (Cst.node `Lean.Parser.Term.explicitBinder bargs) =>
                      if region.size == 1 then fmtTypedBinder "" "" bargs
                      else joinSep (region.toList.map fmtBinderMinimal) " "
                  | _ => joinSep (region.toList.map fmtBinderMinimal) " "
            parensIf (prec > Prec.min) <|
              group <|
                "fun " ++ binderDoc
                  ++ " =>" ++ nest 2 (line ++ fmtTerm Prec.min body)
          else
            Format.nil
      | `Lean.Parser.Term.let =>
          let nt := nonTrivia args
          match nt[1]? with
          | some nameC =>
              let nameF :=
                match getIdent? nameC with
                | some s => text s
                | none   => Format.nil
              let colonIdx := nt.toList.findIdx? (isAtom ":")
              let assignIdx := nt.toList.findIdx? (isAtom ":=")
              let semiIdx  := nt.toList.findIdx? (isAtom ";")
              match assignIdx, semiIdx with
              | some aIdx, some sIdx =>
                  let tyF :=
                    match colonIdx.filter (· < aIdx), colonIdx.bind (fun cI => nt[cI + 1]?) with
                    | some _, some tyC => " : " ++ flatten (fmtTerm Prec.min tyC)
                    | _, _ => Format.nil
                  match nt[aIdx + 1]?, nt[sIdx + 1]? with
                  | some rhsC, some bodyC =>
                      parensIf (prec > Prec.min) <|
                        group ("let " ++ nameF ++ tyF ++ " :="
                                ++ nest 2 (line ++ fmtTerm Prec.min rhsC))
                          ++ ";" ++ line ++ fmtTerm Prec.min bodyC
                  | _, _ => Format.nil
              | _, _ => Format.nil
          | none => Format.nil
      | `«term_=_» =>
          let nt := nonTrivia args
          match nt[0]?, nt[2]? with
          | some a, some b =>
              parensIf (prec > Prec.eq) <|
                group (fmtTerm (Prec.eq + 1) a ++ " =" ++ line
                        ++ fmtTerm (Prec.eq + 1) b)
          | _, _ => Format.nil
      | `«term_+_» =>
          let nt := nonTrivia args
          match nt[0]?, nt[2]? with
          | some a, some b =>
              parensIf (prec > Prec.add) <|
                group (fmtTerm Prec.add a ++ " +" ++ line
                        ++ fmtTerm (Prec.add + 1) b)
          | _, _ => Format.nil
      | _ =>
          match (nonTrivia args)[0]? with
          | some c => fmtTerm prec c
          | none   => Format.nil

partial def fmtTypedBinder (open_ close_ : String) (args : Array Cst) : Format :=
  let nt := nonTrivia args
  let colonIdx := nt.toList.findIdx? (isAtom ":")
  let preColon := match colonIdx with
    | some i => nt.extract 1 i
    | none   => nt.extract 1 nt.size
  let names := preColon.filterMap fun c =>
    match c with
    | .token `ident v               => some (text v)
    | .node `Lean.Parser.Term.hole _ => some "_"
    | _                              => none
  let nameF := joinSep names.toList " "
  match colonIdx.bind (fun i => nt[i + 1]?) with
  | some tyC =>
      open_ ++ nameF ++ " : " ++ flatten (fmtTerm Prec.min tyC) ++ close_
  | none => open_ ++ nameF ++ close_

partial def fmtBinderGroup (cst : Cst) : Format :=
  match cst with
  | .node `Lean.Parser.Term.explicitBinder args => fmtTypedBinder "(" ")" args
  | .node `Lean.Parser.Term.implicitBinder args => fmtTypedBinder "{" "}" args
  | _ => fmtBinder cst

partial def fmtBinder (cst : Cst) : Format :=
  match cst with
  | .token `ident v                          => text v
  | .node `Lean.Parser.Term.hole _           => "_"
  | .node `Lean.Parser.Term.explicitBinder _ => fmtBinderGroup cst
  | .node `Lean.Parser.Term.implicitBinder _ => fmtBinderGroup cst
  | _ => Format.nil

partial def fmtBinderMinimal (cst : Cst) : Format :=
  match cst with
  | .token `ident v                => text v
  | .node `Lean.Parser.Term.hole _ => "_"
  | .node `Lean.Parser.Term.explicitBinder args =>
      if (nonTrivia args).any (isAtom ":") then fmtTypedBinder "(" ")" args
      else fmtTypedBinder "" "" args
  | .node `Lean.Parser.Term.implicitBinder args => fmtTypedBinder "{" "}" args
  | _ => fmtBinder cst

partial def fmtLevel (prec : Nat) (cst : Cst) : Format :=
  match cst with
  | .token `num v   => text v
  | .token `ident v => text v
  | .node k args =>
      match k with
      | `Lean.Parser.Level.num =>
          match (nonTrivia args)[0]? with
          | some c => fmtLevel prec c
          | none   => Format.nil
      | `Lean.Parser.Level.ident =>
          match (nonTrivia args)[0]? with
          | some c => fmtLevel prec c
          | none   => Format.nil
      | `Lean.Parser.Level.paren =>
          let nt := nonTrivia args
          match nt[1]? with
          | some inner => fmtLevel prec inner
          | none       => Format.nil
      | `Lean.Parser.Level.addLit =>
          let nt := nonTrivia args
          match nt[0]?, nt[2]? with
          | some base, some n =>
              parensIf (prec > Prec.add) <|
                fmtLevel (Prec.add + 1) base ++ " + " ++ fmtLevel Prec.app n
          | _, _ => Format.nil
      | `Lean.Parser.Level.max =>
          let nt := nonTrivia args
          let levels := nt.filterMap fun c =>
            if isAtom "max" c ||
               (match c with | .token `ident "max" => true | _ => false) then none
            else some c
          parensIf (prec > Prec.app) <|
            "max " ++ joinSep (levels.toList.map (fmtLevel Prec.app)) " "
      | _ => Format.nil
  | _ => Format.nil

partial def fmtUnivArgs (cst : Cst) : Format :=
  match cst with
  | .node _ args =>
      let nt := nonTrivia args
      let levels := nt.filter fun c =>
        !isAtom "." c && !isAtom "{" c && !isAtom "}" c && !isAtom "," c
      ".{" ++ joinSep (levels.toList.map (fmtLevel Prec.min)) ", " ++ "}"
  | _ => Format.nil

end

def fmtUnivParams (cst : Cst) : Format :=
  match cst with
  | .node _ args =>
      let nt := nonTrivia args
      let idents := nt.filterMap getIdent?
      if idents.isEmpty then Format.nil
      else ".{" ++ joinSep idents.toList ", " ++ "}"
  | _ => Format.nil

def collectSig (cst : Cst) : Array Format × Option Format := Id.run do
  match cst with
  | .node _ args =>
      let nt := nonTrivia args
      let mut binders : Array Format := #[]
      let mut tyOpt : Option Format := none
      let mut i := 0
      let mut stop := false
      while h : i < nt.size && !stop do
        have : i < nt.size := by simp_all
        let c := nt[i]
        match c with
        | .node `Lean.Parser.Term.explicitBinder _ =>
            binders := binders.push (fmtBinderMinimal c)
        | .node `Lean.Parser.Term.implicitBinder _ =>
            binders := binders.push (fmtBinderMinimal c)
        | .token `ident v =>
            binders := binders.push (text v)
        | .node `Lean.Parser.Term.hole _ =>
            binders := binders.push "_"
        | .token `atom ":" =>
            if hh : i + 1 < nt.size then
              tyOpt := some (fmtTerm Prec.min nt[i + 1])
            stop := true
        | _ => ()
        i := i + 1
      return (binders, tyOpt)
  | _ => return (#[], none)

def fmtSig (head : Format) (binders : Array Format) (tyOpt : Option Format) : Format :=
  let binderPart :=
    if binders.isEmpty then Format.nil
    else line ++ fill (joinSep binders.toList line)
  let tyPart :=
    match tyOpt with
    | some t => " :" ++ line ++ t
    | none   => Format.nil
  group (head ++ nest 4 (binderPart ++ tyPart))

def fmtDeclId (cst : Cst) : Format :=
  match cst with
  | .node _ args =>
      let nt := nonTrivia args
      let name :=
        match nt[0]? with
        | some c => match getIdent? c with | some s => text s | none => Format.nil
        | none   => Format.nil
      match nt[1]? with
      | some up => name ++ fmtUnivParams up
      | none    => name
  | _ => Format.nil

def fmtImport (cst : Cst) : Format :=
  match cst with
  | .node _ args =>
      let nt := nonTrivia args
      match nt[1]? with
      | some nameC =>
          match getIdent? nameC with
          | some s => "import " ++ text s
          | none   => Format.nil
      | none => Format.nil
  | _ => Format.nil

def fmtDeclVal (cst : Cst) : Option Format :=
  match cst with
  | .node _ args =>
      match (nonTrivia args)[1]? with
      | some body => some (fmtTerm Prec.min body)
      | none      => none
  | _ => none

def fmtDeclBody (sigF : Format) (body : Cst) : Format :=
  match fmtDeclVal body with
  | some v => group (sigF ++ " :=" ++ nest 2 (line ++ v))
  | none   => sigF

def fmtDefinition (cst : Cst) : Format :=
  match cst with
  | .node _ args =>
      let nt := nonTrivia args
      match nt[1]?, nt[2]?, nt[3]? with
      | some declId, some sig, some body =>
          let (binders, tyOpt) := collectSig sig
          fmtDeclBody (fmtSig ("def " ++ fmtDeclId declId) binders tyOpt) body
      | _, _, _ => Format.nil
  | _ => Format.nil

def fmtExample (cst : Cst) : Format :=
  match cst with
  | .node _ args =>
      let nt := nonTrivia args
      match nt[1]?, nt[2]? with
      | some sig, some body =>
          let (binders, tyOpt) := collectSig sig
          fmtDeclBody (fmtSig "example" binders tyOpt) body
      | _, _ => Format.nil
  | _ => Format.nil

def fmtAxiom (cst : Cst) : Format :=
  match cst with
  | .node _ args =>
      let nt := nonTrivia args
      match nt[1]?, nt[2]? with
      | some declId, some sig =>
          let (binders, tyOpt) := collectSig sig
          fmtSig ("axiom " ++ fmtDeclId declId) binders tyOpt
      | _, _ => Format.nil
  | _ => Format.nil

def fmtCtor (cst : Cst) : Format :=
  match cst with
  | .node _ args =>
      let nt := nonTrivia args
      match nt[1]?, nt[2]? with
      | some nameC, some sig =>
          match getIdent? nameC with
          | some s =>
              let (binders, tyOpt) := collectSig sig
              fmtSig ("| " ++ text s) binders tyOpt
          | none => Format.nil
      | _, _ => Format.nil
  | _ => Format.nil

def fmtInductive (cst : Cst) : Format :=
  match cst with
  | .node _ args =>
      let nt := (nonTrivia args).filter (fun c => !isAtom "where" c)
      match nt[1]?, nt[2]? with
      | some declId, some sig =>
          let (binders, tyOpt) := collectSig sig
          let ctors := nt.toList.drop 3
          let header :=
            fmtSig ("inductive " ++ fmtDeclId declId) binders tyOpt ++ " where"
          let ctorBlock :=
            if ctors.isEmpty then Format.nil
            else nest 2 (line ++ joinSep (ctors.map fmtCtor) line)
          header ++ ctorBlock
      | _, _ => Format.nil
  | _ => Format.nil

def fmtStructField (cst : Cst) : Format :=
  match cst with
  | .node _ args =>
      let nt := nonTrivia args
      match nt[1]?, nt[2]? with
      | some nameC, some sig =>
          match getIdent? nameC with
          | some s =>
              let (binders, tyOpt) := collectSig sig
              "(" ++ fmtSig (text s) binders tyOpt ++ ")"
          | none => Format.nil
      | _, _ => Format.nil
  | _ => Format.nil

def fmtStructure (cst : Cst) : Format :=
  match cst with
  | .node _ args =>
      let nt := (nonTrivia args).filter (fun c => !isAtom "where" c)
      match nt[1]?, nt[2]? with
      | some declId, some sig =>
          let (binders, tyOpt) := collectSig sig
          let fields := nt.toList.drop 3
          let header :=
            fmtSig ("structure " ++ fmtDeclId declId) binders tyOpt ++ " where"
          let fieldBlock :=
            if fields.isEmpty then Format.nil
            else nest 2 (line ++ joinSep (fields.map fmtStructField) line)
          header ++ fieldBlock
      | _, _ => Format.nil
  | _ => Format.nil

partial def fmtCommand (cst : Cst) : Format :=
  match cst with
  | .node k _ =>
      match k with
      | `Lean.Parser.Command.declaration =>
          match (nonTrivia (childrenOf cst))[1]? with
          | some inner => fmtCommand inner
          | none       => Format.nil
      | `Lean.Parser.Command.definition => fmtDefinition cst
      | `Lean.Parser.Command.example    => fmtExample cst
      | `Lean.Parser.Command.axiom      => fmtAxiom cst
      | `Lean.Parser.Command.inductive  => fmtInductive cst
      | `Lean.Parser.Command.structure  => fmtStructure cst
      | `Lean.Parser.Command.import     => fmtImport cst
      | _ => Format.nil
  | _ => Format.nil

def isImport : Cst → Bool
  | .node `Lean.Parser.Command.import _ => true
  | _ => false

def isKnown : Cst → Bool
  | .node `Lean.Parser.Command.declaration _ => true
  | .node `Lean.Parser.Command.definition _  => true
  | .node `Lean.Parser.Command.example _     => true
  | .node `Lean.Parser.Command.axiom _       => true
  | .node `Lean.Parser.Command.inductive _   => true
  | .node `Lean.Parser.Command.structure _   => true
  | .node `Lean.Parser.Command.import _      => true
  | _ => false

def fmtModule (cst : Cst) : Format :=
  let topChildren :=
    match cst with
    | .node `Lean.Parser.Module args =>
        args.flatMap fun c =>
          match c with
          | .node `Lean.Parser.Module.header hargs => hargs
          | _ => #[c]
    | _ => #[]
  let tagged := (tagChildren topChildren).filter fun t => isKnown t.cst
  let rec go : List Tagged → Format
    | []      => Format.nil
    | [t]     => withLeading t.leading (withTrailing t.trailing (fmtCommand t.cst))
    | t :: u :: rest =>
        let cur := withLeading t.leading (withTrailing t.trailing (fmtCommand t.cst))
        let sep := if isImport t.cst && isImport u.cst then line
                   else line ++ line
        cur ++ sep ++ go (u :: rest)
  go tagged.toList

def render (cst : Cst) (width : Nat := 100) : String :=
  let f := fmtModule cst
  let s := Format.pretty f width
  if s.isEmpty then "" else s ++ "\n"

end Qdt.Frontend.Format
