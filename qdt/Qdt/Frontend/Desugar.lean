import Qdt.Frontend.Ast
import Qdt.Frontend.Cst

namespace Qdt.Frontend.Cst

-- TODO: show termination
partial def Term.desugar : Term → Ast.Term
  | .missing src => .missing src
  | .ident src name => .ident src name
  | .app src f a => .app src f.desugar a.desugar
  | .lam src binders body =>
      binders.foldr fun
        | .untyped bSrc name => .lam src (.untyped bSrc name)
        | .typed ⟨groupSrc, names, ty⟩ =>
            let ty := ty.desugar
            names.foldr (fun name => .lam src (.typed ⟨groupSrc, name, ty⟩))
        body.desugar
  | .pi src ⟨groupSrc, names, ty⟩ body =>
      let ty := ty.desugar
      names.foldr (fun name => .pi src ⟨groupSrc, name, ty⟩) body.desugar
  | .arrow src a b =>
      .pi src ⟨src, .anonymous, a.desugar⟩ b.desugar
  | .letE src name tyOpt rhs body =>
      .letE src name (tyOpt.map Term.desugar) rhs.desugar body.desugar
  | .u src => .u src
  | .sigma src ⟨groupSrc, names, ty⟩ body =>
      let ty := ty.desugar
      names.foldr
        (fun name acc =>
          .app src
            (.app src (.ident src `Sigma) ty)
            (.lam src (.typed ⟨groupSrc, name, ty⟩) acc))
        body.desugar
  | .prod src a b => .app src (.app src (.ident src `Prod) a.desugar) b.desugar
  | .pair src a b => .pair src a.desugar b.desugar
  | .eq src a b => .eq src a.desugar b.desugar
  | .natLit src n => n.repeat (.app src (.ident src `Nat.succ)) (.ident src `Nat.zero)
  | .add src a b => .app src (.app src (.ident src `Nat.add) a.desugar) b.desugar
  | .sub src a b => .app src (.app src (.ident src `Nat.sub) a.desugar) b.desugar
  | .mul src a b => .app src (.app src (.ident src `Nat.mul) a.desugar) b.desugar
  | .ann src e ty => .ann src e.desugar ty.desugar
  | .sorry src => .sorry src

def TypedBinderGroup.desugar : TypedBinderGroup → List Ast.TypedBinder :=
  fun ⟨groupSrc, names, ty⟩ =>
    names.map fun name => ⟨groupSrc, name, ty.desugar⟩

def desugarTypedBinderGroupList : List TypedBinderGroup → List Ast.TypedBinder :=
  List.flatMap TypedBinderGroup.desugar

namespace Command

def Import.desugar (i : Import) : Ast.Command.Import where
  src := i.src
  moduleName := i.moduleName

def Definition.desugar (d : Definition) : Ast.Command.Definition where
  src := d.src
  name := d.name
  params := desugarTypedBinderGroupList d.params
  tyOpt := d.tyOpt.map Term.desugar
  body := d.body.desugar

def Example.desugar (e : Example) : Ast.Command.Example where
  src := e.src
  params := desugarTypedBinderGroupList e.params
  tyOpt := e.tyOpt.map Term.desugar
  body := e.body.desugar

def Axiom.desugar (a : Axiom) : Ast.Command.Axiom where
  src := a.src
  name := a.name
  params := desugarTypedBinderGroupList a.params
  ty := a.ty.desugar

def InductiveConstructor.desugar (ctor : InductiveConstructor) : Ast.Command.InductiveConstructor where
  src := ctor.src
  name := ctor.name
  fields := desugarTypedBinderGroupList ctor.fields
  tyOpt := ctor.tyOpt.map Term.desugar

def Inductive.desugar (ind : Inductive) : Ast.Command.Inductive where
  src := ind.src
  name := ind.name
  params := desugarTypedBinderGroupList ind.params
  tyOpt := ind.tyOpt.map Term.desugar
  ctors := ind.ctors.map InductiveConstructor.desugar

def StructureField.desugar (field : StructureField) : Ast.Command.StructureField where
  src := field.src
  name := field.name
  params := desugarTypedBinderGroupList field.params
  ty := field.ty.desugar

def Structure.desugar (str : Structure) : Ast.Command.Structure :=
  {
    src := str.src
    name := str.name
    params := desugarTypedBinderGroupList str.params
    tyOpt := str.tyOpt.map Term.desugar
    fields := str.fields.map StructureField.desugar
  }

def Cmd.desugar : Cmd → Ast.Command.Cmd
  | .import i => .import i.desugar
  | .definition d => .definition d.desugar
  | .example e => .example e.desugar
  | .axiom a => .axiom a.desugar
  | .inductive ind => .inductive ind.desugar
  | .structure str => .structure str.desugar

end Command

def Program.desugar : Program → Ast.Program :=
  List.map Command.Cmd.desugar

end Qdt.Frontend.Cst
