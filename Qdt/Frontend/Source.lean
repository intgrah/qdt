namespace Qdt.Frontend

structure Span where
  startPos : String.Pos.Raw
  endPos : String.Pos.Raw
deriving Repr, Inhabited

abbrev Src := Option Span

/-!
Hashing source spans:

For incremental elaboration, source locations should not affect semantic results.
We therefore hash spans/source locations as a constant.
-/

instance : Hashable Span where
  hash _ := 0

instance : Hashable Src where
  hash _ := 0

end Qdt.Frontend
