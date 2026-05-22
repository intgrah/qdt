module

public import Qdt.Theory.Universe.LE
public import Std.Data.HashMap.Basic

@[expose] public section

namespace Qdt
namespace Universe

def FVMVars : Universe → List UMVarId
  | .zero => []
  | .level _ => []
  | .mvar id => [id]
  | .succ u => u.FVMVars
  | .max u v => u.FVMVars ++ v.FVMVars

abbrev Subst := Std.HashMap UMVarId Universe

namespace Subst

def empty : Subst := ∅

def lookup? (σ : Subst) (m : UMVarId) : Option Universe :=
  Std.HashMap.get? σ m

def assigned (σ : Subst) (m : UMVarId) : Bool := (lookup? σ m).isSome

def insert (σ : Subst) (m : UMVarId) (u : Universe) : Subst :=
  Std.HashMap.insert σ m u

end Subst

instance : Inhabited Subst := ⟨.empty⟩

end Universe
end Qdt
