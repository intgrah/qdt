module

public import Init.Control.Lawful.MonadAttach.Lemmas
public import Init.System.ST
public import Init.System.IO

@[expose] public section

namespace Incremental

variable {ε σ : Type}

/-!
We use `EST` but we can't actually prove anything about it.
Just assume it's well behaved.

If you define a build system that, for example, checks a boolean "cancelled?" flag in another thread,
you need `IO`. Same thing if you need to benchmark queries, with `IO.monoNanosNow` for example.
We aren't relying on these for soundness anyway, if you really want verifiability, just don't use those build systems.
-/

axiom EST.instLawfulMonad : LawfulMonad (EST ε σ)
attribute [instance] EST.instLawfulMonad

axiom EST.lawfulMonadAttach : LawfulMonadAttach (EST ε σ)
attribute [instance] EST.lawfulMonadAttach

instance : LawfulMonad (EIO ε) := inferInstanceAs (LawfulMonad (EST ε IO.RealWorld))
instance : LawfulMonadAttach (EIO ε) := inferInstanceAs (LawfulMonadAttach (EST ε IO.RealWorld))

axiom ST.instLawfulMonad : LawfulMonad (ST σ)
attribute [instance] ST.instLawfulMonad

axiom ST.lawfulMonadAttach : LawfulMonadAttach (ST σ)
attribute [instance] ST.lawfulMonadAttach

instance : LawfulMonad BaseIO := inferInstanceAs (LawfulMonad (ST IO.RealWorld))
instance : LawfulMonadAttach BaseIO := inferInstanceAs (LawfulMonadAttach (ST IO.RealWorld))

end Incremental
