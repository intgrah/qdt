module

public import Qdt.Theory.Syntax
public import Lean.Data.Format

public section

namespace Qdt

open Lean (Name Format ToFormat format)
open Std.Format (text line nest group paren bracket joinSep)

namespace Prec
def min : Nat := 0
def arrow : Nat := 25
def app : Nat := 70
def proj : Nat := 80
def max : Nat := 1024
end Prec

def mkInaccessible (base : Name) (i : Nat) : Name :=
  .num (base.str "_inaccessible") i

def inaccessibleStem? : Name → Option Name
  | .num (.str p "_inaccessible") _ => some p
  | _ => none

def isInaccessible (n : Name) : Bool := (inaccessibleStem? n).isSome

def displayName (ctx : List Name) (n : Name) : Name :=
  match inaccessibleStem? n with
  | none => n
  | some stem =>
      let base := (if stem.isAnonymous then `x else stem).appendAfter "✝"
      let rec go (fuel : Nat) (candidate : Name) : Name :=
        match fuel with
        | 0 => candidate
        | fuel + 1 => if candidate ∈ ctx then go fuel (candidate.appendAfter "✝") else candidate
      go 64 base

def freshName (ctx : List Name) (base : Name) : Name :=
  if isInaccessible base then displayName ctx base
  else
  let stem := if base.isAnonymous then `x else base
  if stem ∉ ctx then stem
  else
    let rec tryNum (n : Nat) : Name :=
      let candidate := stem.appendIndexAfter n
      if candidate ∈ ctx then tryNum (n + 1) else candidate
    partial_fixpoint
    tryNum 1

def lookupName (ctx : List Name) (i : Nat) : Format :=
  match ctx[i]? with
  | some n =>
      if n.isAnonymous then "_"
      else if isInaccessible n then format (displayName (ctx.drop (i + 1)) n)
      else format n
  | none => f!"?{i}"

def parenIf (cond : Bool) : Format → Format :=
  if cond then paren else id

mutual

def Ty.fmt {c : Nat} (ctx : List Name) (ty : Ty c) (prec : Nat) : Format :=
  match ty with
  | .u .zero => "Type"
  | .u i => f!"Type {Universe.fmt i Prec.max}"
  | .pi name bi dom cod =>
      let x := freshName ctx name
      let domFmt := dom.fmt ctx Prec.app
      let codFmt := cod.fmt (x :: ctx) Prec.arrow
      let (l, r) := match bi with | .explicit => ("(", ")") | .implicit => ("{", "}")
      let body :=
        if name.isAnonymous ∧ bi matches .explicit then f!"{domFmt} → {codFmt}"
        else group f!"{l}{x} : {domFmt}{r} → {codFmt}"
      parenIf (prec > Prec.arrow) body
  | .el t => t.fmt ctx prec

def Tm.fmt {c : Nat} (ctx : List Name) (tm : Tm c) (prec : Nat) : Format :=
  match tm with
  | .u' .zero => "Type"
  | .u' i => f!"Type {Universe.fmt i Prec.max}"
  | .var ⟨i, _⟩ => lookupName ctx i
  | .const name us =>
      if us.isEmpty then format name
      else
        let usStrs := us.map (fun u => toString (Universe.fmt u Prec.min))
        toString name ++ ".{" ++ ", ".intercalate usStrs ++ "}"
  | .lam name bi dom body =>
      let x := freshName ctx name
      let domFmt := dom.fmt ctx Prec.arrow
      let bodyFmt := body.fmt (x :: ctx) Prec.min
      let (l, r) := match bi with | .explicit => ("(", ")") | .implicit => ("{", "}")
      let lamFmt := group (nest 2 f!"fun {l}{x} : {domFmt}{r} =>{line}{bodyFmt}")
      parenIf (prec > Prec.arrow) lamFmt
  | .app f a =>
      let fFmt := f.fmt ctx Prec.app
      let aFmt := a.fmt ctx Prec.max
      parenIf (prec > Prec.app) f!"{fFmt} {aFmt}"
  | .pi' name bi dom cod =>
      let x := freshName ctx name
      let domFmt := dom.fmt ctx Prec.app
      let codFmt := cod.fmt (x :: ctx) Prec.arrow
      let (l, r) := match bi with | .explicit => ("(", ")") | .implicit => ("{", "}")
      let body :=
        if name.isAnonymous ∧ bi matches .explicit then f!"{domFmt} → {codFmt}"
        else group f!"{l}{x} : {domFmt}{r} → {codFmt}"
      parenIf (prec > Prec.arrow) body
  | .proj i t => f!"{t.fmt ctx Prec.proj}.{i}"
  | .letE x ty val body =>
      let xFresh := freshName ctx x
      let tyFmt := ty.fmt ctx Prec.min
      let valFmt := val.fmt ctx Prec.min
      let bodyFmt := body.fmt (xFresh :: ctx) Prec.min
      let letFmt := group (nest 2 f!"let {xFresh} : {tyFmt} :={line}{valFmt};") ++ line ++ bodyFmt
      parenIf (prec > Prec.arrow) letFmt
  | .mvar id => f!"?m{id}"

end

instance {c : Nat} : ToFormat (Ty c) where
  format ty := Ty.fmt [] ty Prec.min

instance {c : Nat} : ToFormat (Tm c) where
  format tm := Tm.fmt [] tm Prec.min

instance {c : Nat} : Repr (Ty c) where
  reprPrec ty _ := format ty

instance {c : Nat} : Repr (Tm c) where
  reprPrec tm _ := format tm

instance {c : Nat} : ToString (Ty c) where
  toString ty := Format.pretty (format ty)

instance {c : Nat} : ToString (Tm c) where
  toString tm := Format.pretty (format tm)

end Qdt
