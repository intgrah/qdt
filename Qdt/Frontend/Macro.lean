import Lean
import Qdt.Frontend.Cst

namespace Qdt.Frontend.Macro

/-!
We leverage Lean's meta programming facilities to parse convert Lean syntax into our AST.
-/

open Lean

private def mkNatLit (n : Nat) : Term :=
  Syntax.mkNumLit (toString n)

private def srcNone : Term := mkIdent `none

private def posExpr (p : String.Pos.Raw) : MacroM Term := do
  let n : Term := mkNatLit p.byteIdx
  `(String.Pos.Raw.mk $n)

private def srcFrom (stx : Syntax) : MacroM Term := do
  match stx.getPos?, stx.getTailPos? with
  | some startPos, some endPos =>
      let startPos ← posExpr startPos
      let endPos ← posExpr endPos
      `(some ({ startPos := $startPos, endPos := $endPos } : Qdt.Frontend.Span))
  | _, _ =>
      return srcNone

private def nameFromBinder : Syntax → MacroM Name
  | .ident _ _ id _ => return id
  | .node _ `Lean.Parser.Term.hole _ => return Name.anonymous
  | stx => Macro.throwErrorAt stx s!"expected binder name, got kind {stx.getKind}"

partial def level : Syntax → MacroM Term
  | .node _ `Lean.Parser.Level.paren #[_, l, _] => level l
  | .node _ `null #[l] => level l
  | .ident _ _ n _ => `(Universe.level $(quote n))
  | .node _ `num #[.atom _ raw] =>
      match raw.toNat? with
      | some 0 => `(Universe.zero)
      | some n => `($(mkNatLit n).repeat Universe.succ Universe.zero)
      | none => Macro.throwError s!"invalid level literal {raw}"
  | .node _ `Lean.Parser.Level.num #[.node _ `num #[.atom _ raw]] =>
      match raw.toNat? with
      | some 0 => `(Universe.zero)
      | some n => `($(mkNatLit n).repeat Universe.succ Universe.zero)
      | none => Macro.throwError s!"invalid level literal {raw}"
  | .node _ `Lean.Parser.Level.ident #[.ident _ _ n _] =>
      `(Universe.level $(quote n))
  | .node _ `Lean.Parser.Level.succ #[_, l] => do
      `(Universe.succ $(← level l))
  | .node _ `Lean.Parser.Level.max #[_, .node _ `null #[l1, l2]] => do
      `(Universe.max $(← level l1) $(← level l2))
  | .node _ `Lean.Parser.Level.addLit #[l, _, .node _ `num #[.atom _ raw]] => do
      match raw.toNat? with
      | some n => `($(mkNatLit n).repeat Universe.succ $(← level l))
      | none => Macro.throwError s!"invalid level offset {raw}"
  | stx => Macro.throwErrorAt stx s!"unsupported level syntax, kind {stx.getKind}"

private def levelListExpr (xs : List Term) : MacroM Term := do
  let xsArray := xs.toArray
  `([$[$xsArray],*])

private def parseUnivParams : Syntax → MacroM (List Name)
  | .node _ `null #[] => return []
  | .node _ `null #[.node _ `Lean.Parser.Command.declId #[_, univDecl]] =>
      parseUnivDeclPart univDecl
  | .node _ `Lean.Parser.Command.univDeclSpec #[_, .node _ `null ids, _] =>
      ids.toList.mapM fun
        | .ident _ _ n _ => pure n
        | stx => Macro.throwErrorAt stx s!"expected universe name"
  | stx => Macro.throwErrorAt stx s!"unsupported univParams syntax, kind {stx.getKind}"
where
  parseUnivDeclPart : Syntax → MacroM (List Name)
    | .node _ `null #[] => return []
    | .node _ `null #[.node _ `Lean.Parser.Command.univDeclSpec #[_, .node _ `null ids, _]] =>
        ids.toList.mapM fun
          | .ident _ _ n _ => pure n
          | stx => Macro.throwErrorAt stx s!"expected universe name"
    | stx => Macro.throwErrorAt stx s!"unsupported univDecl syntax, kind {stx.getKind}"

private def parseDeclIdUnivParams : Syntax → MacroM (List Name)
  | .node _ `Lean.Parser.Command.declId #[_, univDecl] =>
      match univDecl with
      | .node _ `null #[] => return []
      | .node _ `null #[.atom _ ".{", .node _ `null ids, .atom _ "}"] =>
          ids.toList.filterMapM fun
            | .ident _ _ n _ => pure (some n)
            | .atom _ "," => pure none
            | stx => Macro.throwErrorAt stx s!"expected universe name, got {stx.getKind}"
      | .node _ `null #[.node _ `Lean.Parser.Command.univDeclSpec #[_, .node _ `null ids, _]] =>
          ids.toList.filterMapM fun
            | .ident _ _ n _ => pure (some n)
            | .atom _ "," => pure none
            | stx => Macro.throwErrorAt stx s!"expected universe name, got {stx.getKind}"
      | stx => Macro.throwErrorAt stx s!"unsupported univDecl syntax, kind {stx.getKind}"
  | stx => Macro.throwErrorAt stx s!"expected declId, got kind {stx.getKind}"

private def parseExplicitUniv : Syntax → MacroM (List Term)
  | .node _ `null #[] => return []
  | .node _ `null #[.node _ `Lean.Parser.Term.explicitUniv #[_, .node _ `null levels, _]] =>
      levels.toList.filterMapM fun
        | .atom _ "," => pure none
        | l => some <$> level l
  | stx => Macro.throwErrorAt stx s!"unsupported explicitUniv syntax, kind {stx.getKind}"

private def typedBinderGroupExpr (groupSrc : Term) (namesWithSrc : List (Term × Name)) (ty : Term) :
    MacroM Term := do
  -- Convert List (Term × Name) to List Term of (Src × Name) pairs
  let pairs ← namesWithSrc.mapM fun (srcTerm, name) =>
    `(($srcTerm, $(quote name)))
  let pairsArray := pairs.toArray
  `(Cst.TypedBinderGroup.mk $groupSrc [$[$pairsArray],*] $ty)

/-- Helper to create namesWithSrc with none for all names (when we don't have individual spans) -/
private def namesWithNoneSrc (names : List Name) : List (Term × Name) :=
  names.map fun name => (mkIdent `none, name)

private def binderGroupUntypedExpr (bSrc : Term) (name : Name) : MacroM Term :=
  `(Cst.BinderGroup.untyped $bSrc $(quote name))

private def binderGroupTypedExpr (typedGroup : Term) : MacroM Term :=
  `(Cst.BinderGroup.typed $typedGroup)

partial def term (stx : Syntax) : MacroM Term := do
  let src ← srcFrom stx
  match stx with
  | .missing => `(Cst.Term.missing $srcNone)
  | .node _ `Lean.Parser.Term.paren #[_, t, _] =>
      term t
  | .ident _ _ id _ =>
      `(Cst.Term.ident $src $(quote id) [])
  | .node _ `Lean.Parser.Term.explicitUniv #[.ident _ _ id _, _, .node _ `null levels, _] =>
      let levels ← levels.toList.filterMapM fun
        | .atom _ "," => pure none
        | l => some <$> level l
      let levels ← levelListExpr levels
      `(Cst.Term.ident $src $(quote id) $levels)
  | .node _ `num #[.atom _ raw] =>
      match raw.toNat? with
      | some n =>
          let n : Term := mkNatLit n
          `(Cst.Term.natLit $src $n)
      | none =>
          Macro.throwErrorAt stx s!"invalid numeric literal {raw}"

  | .node _ `Lean.Parser.Term.app #[f, .node _ `null args] => do
      args.foldlM
        (fun acc a => do `(Cst.Term.app $src $acc $(← term a)))
        (← term f)

  | .node _ `Lean.Parser.Term.fun #[_, .node _ `Lean.Parser.Term.basicFun #[.node _ `null bs, tySpecs, _, body]] =>
      let body ← term body
      match tySpecs with
      | .node _ `null #[] =>
          let bs ← bs.mapM fun b => do
            let bSrc ← srcFrom b
            match b with
            | .ident _ _ id _ => binderGroupUntypedExpr bSrc id
            | .node _ `Lean.Parser.Term.hole _ => binderGroupUntypedExpr bSrc Name.anonymous
            | .node _ `Lean.Parser.Term.typeAscription #[_, nameStx, _, .node _ `null #[ty], _] =>
                let groupSrc ← srcFrom b
                let name ← nameFromBinder nameStx
                let ty ← term ty
                binderGroupTypedExpr (← typedBinderGroupExpr groupSrc (namesWithNoneSrc [name]) ty)
            | _ => Macro.throwErrorAt b s!"unsupported fun binder, kind {b.getKind}"
          `(Cst.Term.lam $src [$[$bs],*] $body)
      | .node _ `null #[.node _ `Lean.Parser.Term.typeSpec #[_, ty]] =>
          let ty ← term ty
          let bs ← bs.mapM nameFromBinder
          let groupSrc ← srcFrom tySpecs
          let typedGroup ← typedBinderGroupExpr groupSrc (namesWithNoneSrc bs.toList) ty
          let bs : List Term := [← binderGroupTypedExpr typedGroup]
          let bsArray := bs.toArray
          `(Cst.Term.lam $src [$[$bsArray],*] $body)
      | _ =>
          Macro.throwErrorAt stx s!"unsupported fun type spec, kind {tySpecs.getKind}"

  | .node _ `Lean.Parser.Term.arrow #[a, _, b] =>
      `(Cst.Term.arrow $src $(← term a) $(← term b))

  | .node _ `Lean.Parser.Term.depArrow #[binder, _, body] =>
      let binder ← match binder with
        | .node _ `Lean.Parser.Term.explicitBinder #[_, .node _ `null names, .node _ `null #[_, ty], .node _ `null #[], _] =>
            let binderSrc ← srcFrom binder
            let names ← names.mapM nameFromBinder
            let ty ← term ty
            typedBinderGroupExpr binderSrc (namesWithNoneSrc names.toList) ty
        | _ => Macro.throwErrorAt binder s!"unsupported dependent arrow binder, kind {binder.getKind}"
      let body ← term body
      `(Cst.Term.pi $src $binder $body)

  | .node _ `Lean.Parser.Term.forall #[_, .node _ `null binders, tySpecs, _, body] =>
      let body ← term body
      match tySpecs with
      | .node _ `null #[.node _ `Lean.Parser.Term.typeSpec #[_, ty]] =>
          let ty ← term ty
          let names ← binders.mapM nameFromBinder
          let groupSrc ← srcFrom tySpecs
          let group ← typedBinderGroupExpr groupSrc (namesWithNoneSrc names.toList) ty
          `(Cst.Term.pi $src $group $body)
      | .node _ `null #[] =>
          let groups ← binders.mapM fun b =>
            match b with
            | .node _ `Lean.Parser.Term.explicitBinder #[_, .node _ `null names, .node _ `null #[_, ty], .node _ `null #[], _] => do
                let groupSrc ← srcFrom b
                let names ← names.mapM nameFromBinder
                let ty ← term ty
                typedBinderGroupExpr groupSrc (namesWithNoneSrc names.toList) ty
            | _ => Macro.throwErrorAt b s!"unsupported forall binder, kind {b.getKind}"
          groups.foldrM
            (fun group acc => `(Cst.Term.pi $src $group $acc))
            body
      | _ =>
          Macro.throwErrorAt stx s!"unsupported forall type spec, kind {tySpecs.getKind}"

  | .node _ `Lean.Parser.Term.typeAscription #[_, e, _, .node _ `null #[ty], _] =>
      `(Cst.Term.ann $src $(← term e) $(← term ty))
  | .node _ `Lean.Parser.Term.type #[_, .node _ `null #[]] =>
      `(Cst.Term.u $src Universe.zero)
  | .node _ `Lean.Parser.Term.type #[_, .node _ `null #[l]] =>
      `(Cst.Term.u $src $(← level l))
  | .node _ `Lean.Parser.Term.sorry _ =>
      `(Cst.Term.sorry $src)
  | .node _ `«term_=_» #[a, _, b] =>
      `(Cst.Term.eq $src $(← term a) $(← term b))
  | .node _ `«term_+_» #[a, _, b] =>
      `(Cst.Term.add $src $(← term a) $(← term b))
  | .node _ `«term_-_» #[a, _, b] =>
      `(Cst.Term.sub $src $(← term a) $(← term b))
  | .node _ `«term_*_» #[a, _, b] =>
      `(Cst.Term.mul $src $(← term a) $(← term b))
  | .node _ `Lean.Parser.Term.let #[_, _, .node _ `Lean.Parser.Term.letDecl #[.node _ `Lean.Parser.Term.letIdDecl #[.node _ `Lean.Parser.Term.letId #[.ident _ _ id _], .node _ `null #[], tySpecs, _, rhs]], _, body] =>
      let tyOpt ←
        match tySpecs with
        | .node _ `null #[] => `(none)
        | .node _ `null #[.node _ `Lean.Parser.Term.typeSpec #[_, ty]] =>
            let ty ← term ty
            `(some $ty)
        | _ => Macro.throwErrorAt stx s!"unsupported let type spec, kind {tySpecs.getKind}"
      let rhs ← term rhs
      let body ← term body
      `(Cst.Term.letE $src $(quote id) $tyOpt $rhs $body)

  | _ =>
      Macro.throwErrorAt stx s!"unsupported term syntax, kind {stx.getKind}"

private def termListExpr (xs : List Term) : MacroM Term := do
  let xsArray := xs.toArray
  `([$[$xsArray],*])

private def typedBinderGroupFromExplicitBinder (termFn : Syntax → MacroM Term) : Syntax → MacroM Term
  | stx@(.node _ `Lean.Parser.Term.explicitBinder #[_, .node _ `null names, .node _ `null #[_, ty], .node _ `null #[], _]) => do
      let groupSrc ← srcFrom stx
      let names ← names.mapM nameFromBinder
      let ty ← termFn ty
      typedBinderGroupExpr groupSrc (namesWithNoneSrc names.toList) ty
  | stx =>
      Macro.throwErrorAt stx s!"unsupported binder group, kind {stx.getKind}"

private def typedBinderGroupsFromNullNode (termFn : Syntax → MacroM Term) : Syntax → MacroM (List Term)
  | .node _ `null bs => do
      let terms ← bs.mapM (typedBinderGroupFromExplicitBinder termFn)
      return terms.toList
  | stx =>
      Macro.throwErrorAt stx s!"expected binder list, got kind {stx.getKind}"

private def declIdName : Syntax → MacroM Name
  | .node _ `Lean.Parser.Command.declId #[.ident _ _ id _, _] =>
      return id
  | stx =>
      Macro.throwErrorAt stx s!"expected declId, got kind {stx.getKind}"

private def optDeclSigInfo (termFn : Syntax → MacroM Term) : Syntax → MacroM (List Term × Option Term)
  | .node _ `Lean.Parser.Command.optDeclSig #[binders, tySpecs] => do
      let params ← typedBinderGroupsFromNullNode termFn binders
      let tyOpt ←
        match tySpecs with
        | .node _ `null #[] =>
            pure none
        | .node _ `null #[.node _ `Lean.Parser.Term.typeSpec #[_, ty]] =>
            do
              let ty ← termFn ty
              pure (some ty)
        | _ =>
            Macro.throwErrorAt tySpecs s!"unsupported declaration type spec, kind {tySpecs.getKind}"
      return (params, tyOpt)
  | stx =>
      Macro.throwErrorAt stx s!"expected optDeclSig, got kind {stx.getKind}"

private def declSigInfo (termFn : Syntax → MacroM Term) : Syntax → MacroM (List Term × Term)
  | .node _ `Lean.Parser.Command.declSig #[binders, .node _ `Lean.Parser.Term.typeSpec #[_, ty]] => do
      let params ← typedBinderGroupsFromNullNode termFn binders
      let ty ← termFn ty
      return (params, ty)
  | stx =>
      Macro.throwErrorAt stx s!"expected declSig, got kind {stx.getKind}"

private def optTermExpr : Option Term → MacroM Term
  | none => `(none)
  | some t => `(some $t)

partial def cmd (stx : Syntax) : MacroM Term := do
  let src ← srcFrom stx
  match stx with
  | .node _ `Lean.Parser.Command.declaration #[_, decl] =>
      cmd decl
  | .node _ `Lean.Parser.Command.definition #[_, declId, optDeclSig, declVal, _] =>
      let name ← declIdName declId
      let univParams ← parseDeclIdUnivParams declId
      let (params, tyOpt?) ← optDeclSigInfo term optDeclSig
      let params ← termListExpr params
      let tyOpt ← optTermExpr tyOpt?
      let rhs ←
        match declVal with
        | .node _ `Lean.Parser.Command.declValSimple #[_, rhs, _, _] => pure rhs
        | _ => Macro.throwErrorAt declVal s!"unsupported def body, kind {declVal.getKind}"
      let body ← term rhs
      `(Cst.Command.Cmd.definition { src := $src, name := $(quote name), univParams := $(quote univParams), params := $params, tyOpt := $tyOpt, body := $body })

  | .node _ `Lean.Parser.Command.example #[_, optDeclSig, declVal] =>
      let (params, tyOpt?) ← optDeclSigInfo term optDeclSig
      let params ← termListExpr params
      let tyOpt ← optTermExpr tyOpt?
      let rhs ←
        match declVal with
        | .node _ `Lean.Parser.Command.declValSimple #[_, rhs, _, _] => pure rhs
        | _ => Macro.throwErrorAt declVal s!"unsupported example body, kind {declVal.getKind}"
      let body ← term rhs
      `(Cst.Command.Cmd.example { src := $src, univParams := [], params := $params, tyOpt := $tyOpt, body := $body })

  | .node _ `Lean.Parser.Command.axiom #[_, declId, declSig] =>
      let name ← declIdName declId
      let univParams ← parseDeclIdUnivParams declId
      let (params, ty) ← declSigInfo term declSig
      let params ← termListExpr params
      `(Cst.Command.Cmd.axiom { src := $src, name := $(quote name), univParams := $(quote univParams), params := $params, ty := $ty })

  | .node _ `Lean.Parser.Command.inductive #[_, declId, optDeclSig, _, .node _ `null ctors, _, _] =>
      let name ← declIdName declId
      let univParams ← parseDeclIdUnivParams declId
      let (params, tyOpt?) ← optDeclSigInfo term optDeclSig
      let params ← termListExpr params
      let tyOpt ← optTermExpr tyOpt?
      let ctors ← ctors.mapM fun ctorStx => do
        let ctorSrc ← srcFrom ctorStx
        match ctorStx with
        | .node _ `Lean.Parser.Command.ctor #[_, _, _, .ident _ _ id _, optDeclSig] =>
            let (cfields, ctyOpt?) ← optDeclSigInfo term optDeclSig
            let cfields ← termListExpr cfields
            let ctyOpt ← optTermExpr ctyOpt?
            `(Cst.Command.InductiveConstructor.mk $ctorSrc $(quote id) $cfields $ctyOpt)
        | _ =>
            Macro.throwErrorAt ctorStx s!"unsupported constructor syntax, kind {ctorStx.getKind}"
      let ctors ← termListExpr ctors.toList
      `(Cst.Command.Cmd.inductive { src := $src, name := $(quote name), univParams := $(quote univParams), params := $params, tyOpt := $tyOpt, ctors := $ctors })

  | .node _ `Lean.Parser.Command.structure #[_, declId, optDeclSig, _, whereFields, _] =>
      let name ← declIdName declId
      let univParams ← parseDeclIdUnivParams declId
      let (params, tyOpt?) ← optDeclSigInfo term optDeclSig
      let params ← termListExpr params
      let tyOpt ← optTermExpr tyOpt?

      let fieldsStx :=
        match whereFields with
        | .node _ `null #[_, _, fs] => fs
        | _ => whereFields

      let fields ←
        match fieldsStx with
        | .node _ `Lean.Parser.Command.structFields #[.node _ `null fs] =>
            let fieldsArray ← fs.mapM fun f => do
              let fSrc ← srcFrom f
              match f with
              | .node _ `Lean.Parser.Command.structExplicitBinder #[_, _, .node _ `null #[idStx@(.ident _ _ id _)], optDeclSig, _, _] =>
                  let nameSrc ← srcFrom idStx
                  let (fparams, ftyOpt?) ← optDeclSigInfo term optDeclSig
                  let fparams ← termListExpr fparams
                  match ftyOpt? with
                  | some fty =>
                      `(Cst.Command.StructureField.mk $fSrc $nameSrc $(quote id) $fparams $fty)
                  | none =>
                      Macro.throwErrorAt f s!"structure field must have a type"
              | _ =>
                  Macro.throwErrorAt f s!"unsupported structure field syntax, kind {f.getKind}"
            termListExpr fieldsArray.toList
        | _ =>
            Macro.throwErrorAt fieldsStx s!"unsupported structure fields, kind {fieldsStx.getKind}"
      `(Cst.Command.Cmd.structure { src := $src, name := $(quote name), univParams := $(quote univParams), params := $params, tyOpt := $tyOpt, fields := $fields })

  | _ =>
      Macro.throwErrorAt stx s!"unsupported command syntax, kind {stx.getKind}"

end Qdt.Frontend.Macro
