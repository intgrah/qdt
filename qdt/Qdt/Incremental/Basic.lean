import Std.Data.DHashMap
import Std.Data.HashMap

namespace Qdt.Incremental

open Std (HashMap DHashMap)

variable {ε α Q : Type} {R : Q → Type} [BEq Q] [LawfulBEq Q] [Hashable Q]

structure Memo (R : Q → Type) (q : Q) where
  value : R q
  deps : HashMap Q UInt64

abbrev Cache (R : Q → Type) [BEq Q] [Hashable Q] :=
  DHashMap Q (Memo R)

structure Engine (ε : Type) (R : Q → Type) where
  cache : Cache R := DHashMap.emptyWithCapacity 1024
  mkCycleError : Q → ε
  fingerprint : ∀ q, R q → UInt64
  isInput : Q → Bool

namespace Engine

def new
    (mkCycleError : Q → ε)
    (fingerprint : ∀ q, R q → UInt64)
    (isInput : Q → Bool := fun _ => false) :
    Engine ε R :=
  {
    cache := DHashMap.emptyWithCapacity 1024
    mkCycleError, fingerprint, isInput
  }

end Engine

structure RunState (ε : Type) (R : Q → Type) where
  engine : Engine ε R
  started : Cache R
  stack : List Q
  deps : HashMap Q UInt64

abbrev BaseM (ε : Type) (R : Q → Type) :=
  StateRefT (RunState ε R) (EIO ε)

structure Fetch (ε : Type) (R : Q → Type) where
  fetch : ∀ q, BaseM ε R (R q)

abbrev TaskM (ε : Type) (R : Q → Type) (α : Type) :=
  ReaderT (Fetch ε R) (BaseM ε R) α

@[inline]
def TaskM.fetch (q : Q) : TaskM ε R (R q) := fun env => env.fetch q

end Qdt.Incremental
