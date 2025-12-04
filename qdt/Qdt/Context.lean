import Qdt.Eval

namespace Qdt

structure Binding where
  name : Option String
  ty : VTy
  deriving Inhabited

structure Context where
  bindings : List Binding
  env : Env
  deriving Inhabited

namespace Context

def lvl (ctx : Context) : Lvl := ctx.bindings.length

def empty : Context := { bindings := [], env := .nil }

def getEnv (ctx : Context) : Env := ctx.env

def bind (name : Option String) (ty : VTy) (ctx : Context) : Context :=
  let var := VTm.neutral (.mk (.var (lvl ctx)) [])
  { bindings := { name, ty } :: ctx.bindings, env := .cons var ctx.env }

def bindAnon (ty : VTy) (ctx : Context) : Context := bind none ty ctx

def define (name : String) (ty : VTy) (value : VTm) (ctx : Context) : Context :=
  { bindings := { name := some name, ty } :: ctx.bindings, env := .cons value ctx.env }

def lookupVar (name : String) (ctx : Context) : Option (Lvl × VTy) :=
  let rec go (bs : List Binding) (i : Nat) : Option (Lvl × VTy) :=
    match bs with
    | [] => none
    | b :: rest =>
        match b.name with
        | some bn => if bn == name then some (lvl ctx - i - 1, b.ty) else go rest (i + 1)
        | none => go rest (i + 1)
  go ctx.bindings 0

def names (ctx : Context) : List String :=
  ctx.bindings.map fun b => b.name.getD "_"

end Context

end Qdt
