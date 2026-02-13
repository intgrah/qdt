import Qdt.Frontend.Ast
import Qdt.Frontend.Cst

namespace Qdt.Frontend.Cst

private def Term.desugar : Term → Ast.Term
  | .missing src => .missing src
  | .ident src name univs => .ident src name univs
  | .app src f a => .app src f.desugar a.desugar
  | .lam src binders body =>
      let expandedBinders : List Ast.Binder := binders.flatMap fun binder =>
        match _ : binder with
        | .untyped bSrc name => [.untyped bSrc name]
        | .typed ⟨_groupSrc, names, ty⟩ =>
            let ty := ty.desugar
            names.map fun (nameSrc, name) => .typed ⟨nameSrc, name, ty⟩
      match expandedBinders with
      | [] => body.desugar
      | first :: rest =>
          let inner := rest.foldr (fun b acc => .lam none b acc) body.desugar
          .lam src first inner
  | .pi src ⟨_groupSrc, names, ty⟩ body =>
      let ty := ty.desugar
      match names with
      | [] => body.desugar
      | (firstSrc, firstName) :: rest =>
          let inner := rest.foldr (fun (nSrc, n) acc => .pi none ⟨nSrc, n, ty⟩ acc) body.desugar
          .pi src ⟨firstSrc, firstName, ty⟩ inner
  | .arrow src a b =>
      .pi src ⟨src, .anonymous, a.desugar⟩ b.desugar
  | .letE src name none rhs body =>
      .letE src name none rhs.desugar body.desugar
  | .letE src name (some ty) rhs body =>
      .letE src name (some ty.desugar) rhs.desugar body.desugar
  | .u src level => .u src level
  | .eq src a b => .eq src a.desugar b.desugar
  | .natLit src n => n.repeat (.app src (.ident src `Nat.succ [])) (.ident src `Nat.zero [])
  | .add src a b => .app src (.app src (.ident src `Nat.add []) a.desugar) b.desugar
  | .sub src a b => .app src (.app src (.ident src `Nat.sub []) a.desugar) b.desugar
  | .mul src a b => .app src (.app src (.ident src `Nat.mul []) a.desugar) b.desugar
  | .ann src e ty => .ann src e.desugar ty.desugar
  | .sorry src => .sorry src
termination_by e => e
decreasing_by
  all_goals try decreasing_tactic
  calc sizeOf ty
    < sizeOf binder := by decreasing_tactic
    _ < sizeOf (lam src binders body) := by decreasing_tactic

private def TypedBinderGroup.desugar : TypedBinderGroup → List Ast.TypedBinder
  | ⟨_groupSrc, names, ty⟩ =>
    names.map fun (nameSrc, name) => ⟨nameSrc, name, ty.desugar⟩

private def desugarTypedBinderGroupList : List TypedBinderGroup → List Ast.TypedBinder :=
  List.flatMap TypedBinderGroup.desugar

namespace Command

private def Import.desugar (i : Import) : Ast.Command.Import where
  src := i.src
  moduleName := i.moduleName

private def Definition.desugar (d : Definition) : Ast.Command.Definition where
  src := d.src
  name := d.name
  univParams := d.univParams
  params := desugarTypedBinderGroupList d.params
  tyOpt := d.tyOpt.map Term.desugar
  body := d.body.desugar

private def Example.desugar (e : Example) : Ast.Command.Example where
  src := e.src
  univParams := e.univParams
  params := desugarTypedBinderGroupList e.params
  tyOpt := e.tyOpt.map Term.desugar
  body := e.body.desugar

private def Axiom.desugar (a : Axiom) : Ast.Command.Axiom where
  src := a.src
  name := a.name
  univParams := a.univParams
  params := desugarTypedBinderGroupList a.params
  ty := a.ty.desugar

private def InductiveConstructor.desugar (ctor : InductiveConstructor) : Ast.Command.InductiveConstructor where
  src := ctor.src
  name := ctor.name
  fields := desugarTypedBinderGroupList ctor.fields
  tyOpt := ctor.tyOpt.map Term.desugar

private def Inductive.desugar (ind : Inductive) : Ast.Command.Inductive where
  src := ind.src
  name := ind.name
  univParams := ind.univParams
  params := desugarTypedBinderGroupList ind.params
  tyOpt := ind.tyOpt.map Term.desugar
  ctors := ind.ctors.map InductiveConstructor.desugar

private def StructureField.desugar (field : StructureField) : Ast.Command.StructureField where
  src := field.src
  nameSrc := field.nameSrc
  name := field.name
  params := desugarTypedBinderGroupList field.params
  ty := field.ty.desugar

private def Structure.desugar (str : Structure) : Ast.Command.Structure where
  src := str.src
  name := str.name
  univParams := str.univParams
  params := desugarTypedBinderGroupList str.params
  tyOpt := str.tyOpt.map Term.desugar
  fields := str.fields.map StructureField.desugar

private def Cmd.desugar : Cmd → Ast.Command.Cmd
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
