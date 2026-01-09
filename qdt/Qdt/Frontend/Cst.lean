import Qdt.Frontend.Source

namespace Qdt.Frontend.Cst

open Lean (Name)

mutual
inductive Term : Type
  | missing : Src → Term
  | ident : Src → Name → Term
  | app : Src → Term → Term → Term
  | lam : Src → List BinderGroup → Term → Term
  | pi : Src → TypedBinderGroup → Term → Term
  | arrow : Src → Term → Term → Term
  | letE : Src → Name → Option Term → Term → Term → Term
  | u : Src → Term
  | sigma : Src → TypedBinderGroup → Term → Term
  | prod : Src → Term → Term → Term
  | pair : Src → Term → Term → Term
  | eq : Src → Term → Term → Term
  | natLit : Src → Nat → Term
  | add : Src → Term → Term → Term
  | sub : Src → Term → Term → Term
  | mul : Src → Term → Term → Term
  | ann : Src → Term → Term → Term
  | sorry : Src → Term
deriving Repr, Inhabited

inductive BinderGroup : Type
  | untyped : Src → Name → BinderGroup
  | typed : TypedBinderGroup → BinderGroup
deriving Repr, Inhabited

inductive TypedBinderGroup : Type
  | mk : Src → List Name → Term → TypedBinderGroup
deriving Repr, Inhabited
end

namespace Command

structure Import where
  src : Src
  moduleName : Name
deriving Repr, Inhabited

structure Definition where
  src : Src
  name : Name
  params : List TypedBinderGroup
  tyOpt : Option Term
  body : Term
deriving Repr, Inhabited

structure Example where
  src : Src
  params : List TypedBinderGroup
  tyOpt : Option Term
  body : Term
deriving Repr, Inhabited

structure Axiom where
  src : Src
  name : Name
  params : List TypedBinderGroup
  ty : Term
deriving Repr, Inhabited

structure InductiveConstructor where
  src : Src
  name : Name
  fields : List TypedBinderGroup
  tyOpt : Option Term
deriving Repr, Inhabited

structure Inductive where
  src : Src
  name : Name
  params : List TypedBinderGroup
  tyOpt : Option Term
  ctors : List InductiveConstructor
deriving Repr, Inhabited

structure StructureField where
  src : Src
  name : Name
  params : List TypedBinderGroup
  ty : Term
deriving Repr, Inhabited

structure Structure where
  src : Src
  name : Name
  params : List TypedBinderGroup
  tyOpt : Option Term
  fields : List StructureField
deriving Repr, Inhabited

inductive Cmd : Type
  | import : Import → Cmd
  | definition : Definition → Cmd
  | example : Example → Cmd
  | axiom : Axiom → Cmd
  | inductive : Inductive → Cmd
  | structure : Structure → Cmd
deriving Repr, Inhabited

end Command

abbrev Program := List Command.Cmd

end Qdt.Frontend.Cst
