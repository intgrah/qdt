module

public import Qdt.Quote

public section

namespace Qdt

open Lean (Name)

variable (q₀ : Key)

namespace Unify

partial def asPattern {n} : Spine n → Option (List (Lvl n)) := fun sp =>
  let rec go : Spine n → Option (List (Lvl n))
    | .nil => some []
    | .app sp (.neutral ⟨.var lvl, .nil⟩) => do
        let rest ← go sp
        if rest.contains lvl then none else some (lvl :: rest)
    | _ => none
  List.reverse <$> go sp

partial def splitPatternPrefix {n} (args : List (VTm n)) :
    List (Lvl n) × List (VTm n) :=
  let rec go (seen : List (Lvl n)) (acc : List (Lvl n)) :
      List (VTm n) → List (Lvl n) × List (VTm n)
    | [] => (acc.reverse, [])
    | a :: rest =>
      match a with
      | VTm.neutral ⟨Head.var lvl, Spine.nil⟩ =>
          if seen.contains lvl then (acc.reverse, a :: rest)
          else go (lvl :: seen) (lvl :: acc) rest
      | _ => (acc.reverse, a :: rest)
  go [] [] args

private def liftRen {n m : Nat} (r : Idx n → Option (Idx m)) :
    Idx (n + 1) → Option (Idx (m + 1)) := fun
  | ⟨0, _⟩ => some ⟨0, Nat.succ_pos _⟩
  | ⟨k + 1, _⟩ => do
      let i ← r ⟨k, by omega⟩
      some ⟨i.val + 1, by have := i.isLt; omega⟩

mutual
private partial def renameTy {n m : Nat} (r : Idx n → Option (Idx m)) : Ty n → Option (Ty m)
  | .u u => some (.u u)
  | .pi x dom cod => do
      let dom ← renameTy r dom
      let cod ← renameTy (liftRen r) cod
      some (.pi x dom cod)
  | .el t => Ty.el <$> renameTm r t

private partial def renameTm {n m : Nat} (r : Idx n → Option (Idx m)) : Tm n → Option (Tm m)
  | .u' u => some (.u' u)
  | .var i => Tm.var <$> r i
  | .const c us => some (.const c us)
  | .lam x ty body => do
      let ty ← renameTy r ty
      let body ← renameTm (liftRen r) body
      some (.lam x ty body)
  | .app f a => do
      let f ← renameTm r f
      let a ← renameTm r a
      some (.app f a)
  | .pi' x a b => do
      let a ← renameTm r a
      let b ← renameTm (liftRen r) b
      some (.pi' x a b)
  | .proj i t => (Tm.proj i) <$> renameTm r t
  | .letE x ty rhs body => do
      let ty ← renameTy r ty
      let rhs ← renameTm r rhs
      let body ← renameTm (liftRen r) body
      some (.letE x ty rhs body)
  | .mvar id => some (.mvar id)
end

mutual
private partial def tyContainsMeta {n} (id : MVarId) : Ty n → Bool
  | .u _ => false
  | .pi _ a b => tyContainsMeta id a || tyContainsMeta id b
  | .el t => tmContainsMeta id t

private partial def tmContainsMeta {n} (id : MVarId) : Tm n → Bool
  | .u' _ => false
  | .var _ => false
  | .const _ _ => false
  | .lam _ ty body => tyContainsMeta id ty || tmContainsMeta id body
  | .app f a => tmContainsMeta id f || tmContainsMeta id a
  | .pi' _ a b => tmContainsMeta id a || tmContainsMeta id b
  | .proj _ t => tmContainsMeta id t
  | .letE _ ty rhs body => tyContainsMeta id ty || tmContainsMeta id rhs || tmContainsMeta id body
  | .mvar id' => id == id'
end

partial def wrapLams : (a : Nat) → Tm a → Tm 0
  | 0, t => t
  | k + 1, t => wrapLams k (.lam .anonymous (.u .zero) t)

partial def solveFlexRigid {n} (id : MVarId) (xs : List (Lvl n))
    (rhs : VTm n) : ElabM q₀ Bool := do
  let rhs ← rhs.quote q₀
  let a := xs.length
  let entries : List (Nat × Idx a) :=
    (xs.zip (List.finRange a)).map fun (lvl, i) =>
      (n - 1 - lvl.val,
       ⟨a - 1 - i.val,
        by have := i.isLt; omega⟩)
  let r : Idx n → Option (Idx a) := fun ⟨k, _⟩ =>
    entries.lookup k
  let some body := renameTm r rhs
    | return false
  if tmContainsMeta id body then return false
  let solution := wrapLams a body
  assignMeta q₀ id solution
  return true

structure PatternPrefix {n} (args : List (VTm n)) where
  prefixLen : Nat
  prefixLvls : List (Lvl n)
  prefixLen_le : prefixLen ≤ args.length
  prefixLvls_len : prefixLvls.length = prefixLen

instance {n} (args : List (VTm n)) : Nonempty (PatternPrefix args) :=
  ⟨{ prefixLen := 0, prefixLvls := [], prefixLen_le := Nat.zero_le _,
     prefixLvls_len := rfl }⟩

partial def patternVarPrefix {n} (_mvarArity : Nat) (args : List (VTm n)) :
    PatternPrefix args :=
  let rec go (consumed : Nat) (seen : List (Lvl n)) (acc : List (Lvl n))
      (remaining : List (VTm n))
      (hLen : consumed + remaining.length = args.length)
      (hAcc : acc.length = consumed) : PatternPrefix args :=
    match remaining, hLen with
    | [], hLen =>
        { prefixLen := consumed, prefixLvls := acc.reverse,
          prefixLen_le := by simp at hLen; omega,
          prefixLvls_len := by simp [hAcc] }
    | (a :: rest), hLen =>
      match a with
      | VTm.neutral ⟨Head.var lvl, Spine.nil⟩ =>
          if seen.contains lvl then
            { prefixLen := consumed, prefixLvls := acc.reverse,
              prefixLen_le := by simp at hLen; omega,
              prefixLvls_len := by simp [hAcc] }
          else
            go (consumed + 1) (lvl :: seen) (lvl :: acc) rest
              (by simp at hLen ⊢; omega)
              (by simp [hAcc])
      | _ =>
          { prefixLen := consumed, prefixLvls := acc.reverse,
            prefixLen_le := by simp at hLen; omega,
            prefixLvls_len := by simp [hAcc] }
  go 0 [] [] args (by simp) (by simp)

partial def processConstApprox {n} (id : MVarId) {args : List (VTm n)}
    (pp : PatternPrefix args) (rhs : Tm n) :
    ElabM q₀ (Option ((a : Nat) × Tm a)) := do
  let numArgs := args.length
  let defaultCase : ElabM q₀ (Option ((a : Nat) × Tm a)) := do
    let r : Idx n → Option (Idx numArgs) := fun _ => none
    let some body := renameTm r rhs | return none
    if tmContainsMeta id body then return none
    return some ⟨numArgs, body⟩
  if pp.prefixLen = 0 then return ← defaultCase
  let hLe : pp.prefixLen ≤ numArgs := pp.prefixLen_le
  let entries : List (Nat × Idx numArgs) :=
    (pp.prefixLvls.zip (List.finRange pp.prefixLen)).map fun (lvl, i) =>
      (n - 1 - lvl.val,
       ⟨numArgs - 1 - i.val,
        by have := i.isLt; omega⟩)
  let r : Idx n → Option (Idx numArgs) := fun ⟨k, _⟩ =>
    entries.lookup k
  match renameTm r rhs with
  | some body =>
      if tmContainsMeta id body then return ← defaultCase
      return some ⟨numArgs, body⟩
  | none => defaultCase

partial def solveMVar {n} (id : MVarId) (sp : Spine n) (rhs : VTm n) :
    ElabM q₀ (Option ((a : Nat) × Tm a)) := do
  let rhs ← rhs.quote q₀
  let args := (sp.toAppList).getD []
  let (arity, numScopeArgs) := match ← getMetaInfo q₀ id with
    | some info => (info.arity, info.numScopeArgs)
    | none => (0, 0)
  let pp := patternVarPrefix arity args
  if pp.prefixLen = args.length then
    let a := args.length
    let entries : List (Nat × Idx a) :=
      (pp.prefixLvls.zip (List.finRange a)).map fun (lvl, i) =>
        (n - 1 - lvl.val,
         ⟨a - 1 - i.val,
          by have := i.isLt; omega⟩)
    let r : Idx n → Option (Idx a) := fun ⟨k, _⟩ =>
      entries.lookup k
    match renameTm r rhs with
    | some body =>
        if tmContainsMeta id body then return none
        return some ⟨a, body⟩
    | none => return none
  else
    if numScopeArgs != args.length then
      processConstApprox q₀ id pp rhs
    else
      return none


end Unify

end Qdt
