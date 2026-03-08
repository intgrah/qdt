import Qdt.Lsp.Test

open Qdt.Lsp.Test

#eval test do

setText qdt!(
example : Type 2 → Type → Type 1 := fun a b => Type
--    ^^^^^   ^^^^^^   ^^^^   ^^^^^^^^^^^^^^^^^^
--2345678901234567890123456789012345678901234567890
)

noDiagnostics

-- example :
noHover ⟨1, 6⟩
noHover ⟨1, 7⟩
noHover ⟨1, 8⟩
noHover ⟨1, 9⟩

-- Type 2
hover ⟨1, 10⟩ "Type 2 : Type 3"
hover ⟨1, 14⟩ "Type 2 : Type 3"
hover ⟨1, 15⟩ "Type 2 : Type 3"

-- →
hover ⟨1, 16⟩ "Type 3"
hover ⟨1, 17⟩ "Type 3"
hover ⟨1, 18⟩ "Type 3"

-- Type
hover ⟨1, 19⟩ "Type : Type 1"

-- →
hover ⟨1, 23⟩ "Type 2"
hover ⟨1, 24⟩ "Type 2"
hover ⟨1, 25⟩ "Type 2"

-- Type 1
hover ⟨1, 26⟩ "Type 1 : Type 2"
hover ⟨1, 30⟩ "Type 1 : Type 2"
hover ⟨1, 31⟩ "Type 1 : Type 2"

-- :=
noHover ⟨1, 32⟩
noHover ⟨1, 33⟩
noHover ⟨1, 34⟩
noHover ⟨1, 35⟩

-- fun a b
hover ⟨1, 36⟩ "Type 2 → Type → Type 1"
hover ⟨1, 37⟩ "Type 2 → Type → Type 1"
hover ⟨1, 38⟩ "Type 2 → Type → Type 1"
hover ⟨1, 39⟩ "Type 2 → Type → Type 1"
hover ⟨1, 40⟩ "a : Type 2"
hover ⟨1, 41⟩ "Type 2 → Type → Type 1"
hover ⟨1, 42⟩ "b : Type"

-- =>
hover ⟨1, 43⟩ "Type 2 → Type → Type 1"
hover ⟨1, 44⟩ "Type 2 → Type → Type 1"
hover ⟨1, 45⟩ "Type 2 → Type → Type 1"
hover ⟨1, 46⟩ "Type 2 → Type → Type 1"

-- Type
hover ⟨1, 47⟩ "Type : Type 1"
