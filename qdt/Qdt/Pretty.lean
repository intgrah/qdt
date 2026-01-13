import Qdt.MLTT.Syntax
import Lean.Data.Format
import Lean.Data.Name

namespace Qdt

open Lean (Name Format ToFormat format)
open Std.Format (text line nest group paren bracket joinSep)

/-! ## Precedence levels for pretty printing -/

/-- Precedence levels for expression pretty printing.
Higher numbers bind tighter. -/
inductive Prec : Type
  | min   : Prec  -- lowest: top-level, let bodies
  | arrow : Prec  -- →, let
  | app   : Prec  -- function application
  | proj  : Prec  -- projection .i
  | max   : Prec  -- highest: atoms, parenthesized
  deriving Repr, BEq, Ord

namespace Prec

instance : OfNat Prec 0 := ⟨.min⟩
instance : OfNat Prec 1 := ⟨.arrow⟩
instance : OfNat Prec 2 := ⟨.app⟩
instance : OfNat Prec 3 := ⟨.proj⟩
instance : OfNat Prec 4 := ⟨.max⟩

/-- Returns true if parentheses are needed when a child expression with
    precedence `inner` appears in a context with precedence `outer`. -/
def needsParens (outer inner : Prec) : Bool :=
  compare outer inner == .gt

end Prec

/-! ## Name context for de Bruijn indices -/

/-- Generate a fresh name that doesn't conflict with names in the context. -/
partial def freshName (ctx : List Name) (base : Name) : Name :=
  let stem := if base.isAnonymous then `x else base
  if !ctx.contains stem then stem
  else
    let rec tryNum (n : Nat) : Name :=
      let candidate := stem.appendIndexAfter n
      if ctx.contains candidate then tryNum (n + 1) else candidate
    tryNum 1

/-- Look up a name for a de Bruijn index. -/
def lookupName (ctx : List Name) (i : Nat) : Format :=
  match ctx[i]? with
  | some n => if n.isAnonymous then f!"_" else format n
  | none   => f!"?{i}"

/-! ## Pretty printing for Ty and Tm -/

/-- Wrap in parentheses if needed based on precedence. -/
def parenIf (cond : Bool) (f : Format) : Format :=
  if cond then paren f else f

mutual

/-- Pretty print a type with precedence and name context. -/
partial def Ty.fmt {c : Nat} (prec : Prec) (ctx : List Name) : Ty c → Format
  | .u => "Type"
  | .pi ⟨name, dom⟩ cod =>
      let x := freshName ctx name
      let domFmt := dom.fmt .app ctx
      let codFmt := cod.fmt .arrow (x :: ctx)
      let body :=
        if name.isAnonymous then
          domFmt ++ " → " ++ codFmt
        else
          group ("(" ++ format x ++ " : " ++ domFmt ++ ")" ++ " → " ++ codFmt)
      parenIf (prec.needsParens .arrow) body
  | .el t => t.fmt prec ctx

/-- Pretty print a term with precedence and name context. -/
partial def Tm.fmt {c : Nat} (prec : Prec) (ctx : List Name) : Tm c → Format
  | .var ⟨i, _⟩ => lookupName ctx i

  | .const name => format name

  | .lam ⟨name, dom⟩ body =>
      let x := freshName ctx name
      let domFmt := dom.fmt .arrow ctx
      let bodyFmt := body.fmt .min (x :: ctx)
      let lamFmt := group (nest 2 ("fun " ++ format x ++ " : " ++ domFmt ++ " =>" ++ line ++ bodyFmt))
      parenIf (prec.needsParens .arrow) lamFmt

  | .app f a =>
      let fFmt := f.fmt .app ctx
      let aFmt := a.fmt .max ctx
      parenIf (prec.needsParens .app) (fFmt ++ " " ++ aFmt)

  | .pi' name dom cod =>
      let x := freshName ctx name
      let domFmt := dom.fmt .app ctx
      let codFmt := cod.fmt .arrow (x :: ctx)
      let body :=
        if name.isAnonymous then
          domFmt ++ " → " ++ codFmt
        else
          group ("(" ++ format x ++ " : " ++ domFmt ++ ")" ++ " → " ++ codFmt)
      parenIf (prec.needsParens .arrow) body

  | .proj i t =>
      let tFmt := t.fmt .proj ctx
      tFmt ++ "." ++ format i

  | .letE x ty val body =>
      let xFresh := freshName ctx x
      let tyFmt := ty.fmt .min ctx
      let valFmt := val.fmt .min ctx
      let bodyFmt := body.fmt .min (xFresh :: ctx)
      let letFmt := group (nest 2 (
        "let " ++ format xFresh ++ " : " ++ tyFmt ++ " :=" ++ line ++ valFmt ++ ";"
      ) ++ line ++ bodyFmt)
      parenIf (prec.needsParens .arrow) letFmt

end

/-! ## String-based API (for error messages) -/

/-- Pretty print a type to a string with precedence and name context. -/
def Ty.pp {c : Nat} (prec : Prec) (ctx : List Name) (ty : Ty c) : String :=
  Format.pretty (Ty.fmt prec ctx ty)

/-- Pretty print a term to a string with precedence and name context. -/
def Tm.pp {c : Nat} (prec : Prec) (ctx : List Name) (tm : Tm c) : String :=
  Format.pretty (Tm.fmt prec ctx tm)

/-! ## ToFormat and ToString instances -/

instance {c : Nat} : ToFormat (Ty c) where
  format ty := Ty.fmt .min [] ty

instance {c : Nat} : ToFormat (Tm c) where
  format tm := Tm.fmt .min [] tm

instance {c : Nat} : ToString (Ty c) where
  toString ty := Format.pretty (Ty.fmt .min [] ty)

instance {c : Nat} : ToString (Tm c) where
  toString tm := Format.pretty (Tm.fmt .min [] tm)

/-- Pretty print a type to a string. -/
def Ty.pretty {c : Nat} (ty : Ty c) : String :=
  Format.pretty (Ty.fmt .min [] ty)

/-- Pretty print a term to a string. -/
def Tm.pretty {c : Nat} (tm : Tm c) : String :=
  Format.pretty (Tm.fmt .min [] tm)

end Qdt
