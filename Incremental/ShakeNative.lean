module

public import Incremental.Shake

@[expose] public section

namespace Incremental

namespace ShakeNative

open Shake (Memo Store)

variable {Q : Type} {R : Q → Type}
  [BEq Q] [LawfulBEq Q] [Hashable Q] [∀ q, Hashable (R q)]

@[extern "lean_shake_build"]
opaque build :
    (∀ q, Option (Task Monad Q R (R q))) →
    (target : Q) →
    Store Q R →
    Except BuildError (R target × Store Q R)

end ShakeNative
