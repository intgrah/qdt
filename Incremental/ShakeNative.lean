module

public import Incremental.Shake

@[expose] public section

namespace Incremental

namespace ShakeNative

open Shake (Memo Store)

variable {Q : Type} {R : Q → Type}
  [BEq Q] [LawfulBEq Q] [Hashable Q] [∀ q, Hashable (R q)]

@[extern "lean_shake_build"]
opaque build' :
    Tasks Monad Q R →
    ∀ q,
    Store Q R →
    Except BuildError (R q × Store Q R)

@[always_inline]
def build :
    Tasks Monad Q R →
    ∀ q,
    StateT (Store Q R) (Except BuildError) (R q) :=
  build'

end ShakeNative
