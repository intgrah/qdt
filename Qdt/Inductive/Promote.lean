module

public import Qdt.Inductive.Constructor

public section

namespace Qdt

open Lean (Name)

def ctorPromotionPrefix {n : Nat} (indName : Name) (numIndices : Nat) (ctorTy : Ty n) : Nat :=
  let ⟨fieldEnd, fields, retTy⟩ := ctorTy.getTele
  if fields.any (fun ⟨_, _, ty⟩ => ty.hasIndOcc indName) then 0
  else
    let numFields := fieldEnd - n
    match retTy with
    | .el resTm =>
        let (_, args) := resTm.getAppArgs
        if args.length != n + numIndices then 0
        else
          let indexArgs := args.drop n |>.take (min numIndices numFields)
          let hits := indexArgs.mapIdx fun i arg =>
            let expectedIdx := numFields - 1 - i
            match arg with
            | .var ⟨k, _⟩ => k == expectedIdx
            | _ => false
          hits.takeWhile id |>.length
    | _ => 0

def computeNumPromoted {n : Nat} (indName : Name) (numIndices : Nat) (ctorTys : List (Name × Ty n)) :
    { k : Nat // k ≤ numIndices } :=
  match ctorTys with
  | [] => ⟨0, Nat.zero_le _⟩
  | _ :: _ =>
      ctorTys.foldl (init := ⟨numIndices, Nat.le_refl _⟩) fun ⟨acc, h⟩ (_, ty) =>
        ⟨min acc (ctorPromotionPrefix indName numIndices ty), Nat.le_trans (Nat.min_le_left ..) h⟩

def ctxToList {a b : Nat} {α : Type} (f : ∀ {n}, Name × BinderInfo × Ty n → α) (tele : Ctx a b) : List α :=
  go [] tele
where
  go (acc : List α) : {b' : Nat} → Ctx a b' → List α
    | _, .nil => acc
    | _, .snoc ts t => go (f t :: acc) ts

def ctorLeadingPlicities {n : Nat} (numPromoted : Nat) (ctorTy : Ty n) : List BinderInfo :=
  let ⟨_, fields, _⟩ := ctorTy.getTele
  (ctxToList (·.snd.fst) fields).take numPromoted

end Qdt
