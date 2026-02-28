import Qdt.Frontend.Ast

namespace Qdt.Lsp

open Lean (Name)
open Frontend (Ast Path)

def astAtPath (prog : Array Ast) (path : Path) : Option Ast := do
  if path.isEmpty then failure
  let cmdIdx :: rest := path | failure
  if h : cmdIdx < prog.size then
    let mut current := prog[cmdIdx]
    for idx in rest do
      match current with
      | .node _ children =>
          if hj : idx < children.size then
            current := children[idx]
          else failure
      | _ => failure
    return current
  else failure

def isAtomicNode : Ast → Bool
  | .ident _ => true
  | .node `Binder.typed _ => true
  | .node `Binder.untyped _ => true
  | .node `Term.type _ => true
  | .node `Level.name _ => true
  | _ => false

def getAtomicName : Ast → Option String
  | .ident n => if n.isAnonymous then none else some (toString n)
  | .node `Binder.typed cs => let n := cs[0]!.getName; if n.isAnonymous then none else some (toString n)
  | .node `Binder.untyped cs => let n := cs[0]!.getName; if n.isAnonymous then none else some (toString n)
  | .node `Term.type _ => some "Type"
  | .node `Level.name cs => let n := cs[0]!.getName; if n.isAnonymous then none else some (toString n)
  | _ => none

def formatHover (ast : Option Ast) (ty : String) : String :=
  match ast with
  | some a =>
      if isAtomicNode a then
        match getAtomicName a with
        | some name => s!"{name} : {ty}"
        | none => ty
      else ty
  | none => ty

end Qdt.Lsp
