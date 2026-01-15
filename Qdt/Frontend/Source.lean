namespace Qdt.Frontend

structure Span where
  startPos : String.Pos.Raw
  endPos : String.Pos.Raw
deriving Repr, Inhabited

abbrev Src := Option Span

instance : Hashable Span where
  hash s := mixHash (hash s.startPos.byteIdx) (hash s.endPos.byteIdx)

instance : Hashable Src where hash
  | none => 0
  | some s => hash s

end Qdt.Frontend
