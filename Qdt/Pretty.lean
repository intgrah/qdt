import Qdt.MLTT.Syntax
import Lean.Data.Format
import Lean.Data.Name

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

def freshName (ctx : List Name) (base : Name) : Name :=
  let stem := if base.isAnonymous then `x else base
  if !ctx.contains stem then stem
  else
    let rec tryNum : Nat → Nat → Name
      | 0, n => stem.appendIndexAfter n
      | fuel + 1, n =>
          let candidate := stem.appendIndexAfter n
          if ctx.contains candidate then tryNum fuel (n + 1) else candidate
    tryNum (ctx.length + 1) 1

def lookupName (ctx : List Name) (i : Nat) : Format :=
  match ctx[i]? with
  | some n => if n.isAnonymous then "_" else format n
  | none   => f!"?{i}"

def parenIf (cond : Bool) : Format → Format :=
  if cond then paren else id

mutual

def Ty.fmt {c : Nat} (ctx : List Name) (ty : Ty c) (prec : Nat) : Format :=
  match ty with
  | .u _ .zero => "Type"
  | .u _ i => f!"Type {Universe.reprPrec i Prec.max}"
  | .pi _ ⟨_, name, dom⟩ cod =>
      let x := freshName ctx name
      let domFmt := dom.fmt ctx Prec.app
      let codFmt := cod.fmt (x :: ctx) Prec.arrow
      let body :=
        if name.isAnonymous then f!"{domFmt} → {codFmt}"
        else group f!"({x} : {domFmt}) → {codFmt}"
      parenIf (prec > Prec.arrow) body
  | .el _ t => t.fmt ctx prec

def Tm.fmt {c : Nat} (ctx : List Name) (tm : Tm c) (prec : Nat) : Format :=
  match tm with
  | .u' _ .zero => "Type"
  | .u' _ i => f!"Type {Universe.reprPrec i Prec.max}"
  | .var _ ⟨i, _⟩ => lookupName ctx i
  | .const _ name us =>
      if us.isEmpty then format name
      else
        let usStrs := us.map (fun u => toString (Universe.reprPrec u Prec.min))
        toString name ++ ".{" ++ ", ".intercalate usStrs ++ "}"
  | .lam _ ⟨_, name, dom⟩ body =>
      let x := freshName ctx name
      let domFmt := dom.fmt ctx Prec.arrow
      let bodyFmt := body.fmt (x :: ctx) Prec.min
      let lamFmt := group (nest 2 f!"fun {x} : {domFmt} =>{line}{bodyFmt}")
      parenIf (prec > Prec.arrow) lamFmt
  | .app _ f a =>
      let fFmt := f.fmt ctx Prec.app
      let aFmt := a.fmt ctx Prec.max
      parenIf (prec > Prec.app) f!"{fFmt} {aFmt}"
  | .pi' _ ⟨_, name, dom⟩ cod =>
      let x := freshName ctx name
      let domFmt := dom.fmt ctx Prec.app
      let codFmt := cod.fmt (x :: ctx) Prec.arrow
      let body :=
        if name.isAnonymous then f!"{domFmt} → {codFmt}"
        else group f!"({x} : {domFmt}) → {codFmt}"
      parenIf (prec > Prec.arrow) body
  | .proj _ i t => f!"{t.fmt ctx Prec.proj}.{i}"
  | .letE _ x ty val body =>
      let xFresh := freshName ctx x
      let tyFmt := ty.fmt ctx Prec.min
      let valFmt := val.fmt ctx Prec.min
      let bodyFmt := body.fmt (xFresh :: ctx) Prec.min
      let letFmt := group (nest 2 f!"let {xFresh} : {tyFmt} :={line}{valFmt};") ++ line ++ bodyFmt
      parenIf (prec > Prec.arrow) letFmt

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
