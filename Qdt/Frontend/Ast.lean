import Qdt.Frontend.Source
import Qdt.MLTT.Universe

namespace Qdt.Frontend.Ast

open Lean (Name)

mutual
inductive Term : Type
  | missing : Src → Term
  | ident : Src → Name → List Universe → Term
  | app : Src → Term → Term → Term
  | lam : Src → Binder → Term → Term
  | pi : Src → TypedBinder → Term → Term
  | letE : Src → Name → Option Term → Term → Term → Term
  | u : Src → Universe → Term
  | pair : Src → Term → Term → Term
  | eq : Src → Term → Term → Term
  | ann : Src → Term → Term → Term
  | sorry : Src → Term
deriving Repr, Inhabited, Hashable

inductive Binder : Type
  | untyped : Src → Name → Binder
  | typed : TypedBinder → Binder
deriving Repr, Inhabited, Hashable

structure TypedBinder where
  src : Src
  name : Name
  ty : Term
deriving Repr, Inhabited, Hashable

end

def Term.src : Term → Src
  | .missing src
  | .ident src _ _
  | .app src _ _
  | .lam src _ _
  | .pi src _ _
  | .letE src _ _ _ _
  | .u src _
  | .pair src _ _
  | .eq src _ _
  | .ann src _ _
  | .sorry src
    => src

namespace Command

structure Import where
  src : Src
  moduleName : Name
deriving Repr, Inhabited, Hashable

structure Definition where
  src : Src
  name : Name
  univParams : List Name
  params : List TypedBinder
  tyOpt : Option Term
  body : Term
deriving Repr, Inhabited, Hashable

structure Example where
  src : Src
  univParams : List Name
  params : List TypedBinder
  tyOpt : Option Term
  body : Term
deriving Repr, Inhabited, Hashable

structure Axiom where
  src : Src
  name : Name
  univParams : List Name
  params : List TypedBinder
  ty : Term
deriving Repr, Inhabited, Hashable

structure InductiveConstructor where
  src : Src
  name : Name
  fields : List TypedBinder
  tyOpt : Option Term
deriving Repr, Inhabited, Hashable

structure Inductive where
  src : Src
  name : Name
  univParams : List Name
  params : List TypedBinder
  tyOpt : Option Term
  ctors : List InductiveConstructor
deriving Repr, Inhabited, Hashable

structure StructureField where
  src : Src
  name : Name
  params : List TypedBinder
  ty : Term
deriving Repr, Inhabited, Hashable

structure Structure where
  src : Src
  name : Name
  univParams : List Name
  params : List TypedBinder
  tyOpt : Option Term
  fields : List StructureField
deriving Repr, Inhabited, Hashable

inductive Cmd : Type
  | import : Import → Cmd
  | definition : Definition → Cmd
  | example : Example → Cmd
  | axiom : Axiom → Cmd
  | inductive : Inductive → Cmd
  | structure : Structure → Cmd
deriving Repr, Inhabited, Hashable

end Command

abbrev Program := List Command.Cmd

end Qdt.Frontend.Ast
