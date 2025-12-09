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

def lvl (ctx : Context) : Nat := ctx.bindings.length

def empty : Context where
  bindings := []
  env := .nil

def getEnv (ctx : Context) : Env := ctx.env

def bind (name : Option String) (ty : VTy) (ctx : Context) : Context where
  bindings := { name, ty } :: ctx.bindings
  env := .cons (VTm.neutral (.mk (.var (lvl ctx)) [])) ctx.env

def define (name : String) (ty : VTy) (value : VTm) (ctx : Context) : Context where
  bindings := { name := some name, ty } :: ctx.bindings
  env := .cons value ctx.env

def lookupVar (name : String) (ctx : Context) : Option (Nat × VTy) :=
  let rec go  (i : Nat) : List Binding → Option (Nat × VTy)
    | [] => none
    | b :: rest =>
        match b.name with
        | some bn => if bn == name then some (lvl ctx - i - 1, b.ty) else go (i + 1) rest
        | none => go (i + 1) rest
  go 0 ctx.bindings

def names (ctx : Context) : List String :=
  ctx.bindings.map fun b => b.name.getD "_"

end Context

structure GlobalEntry where
  ty : VTy
  value : VTm

structure GlobalEnv where
  entries : List (String × GlobalEntry)

namespace GlobalEnv

def empty : GlobalEnv := { entries := [] }

def add (env : GlobalEnv) (name : String) (ty : VTy) (value : VTm) : GlobalEnv :=
  { entries := (name, { ty, value }) :: env.entries }

def find? (env : GlobalEnv) (name : String) : Option GlobalEntry :=
  (env.entries.find? (fun p => p.fst == name)).map Prod.snd

def unfold (env : GlobalEnv) (name : String) : Option VTm :=
  (find? env name).map (·.value)

end GlobalEnv

end Qdt
