import Lean

open Lean (Name)

inductive Level where
  | zero
  | succ (l : Nat)
  | max (l₁ l₂ : Nat)
  | param (name : Nat)
deriving Inhabited

inductive Expr where
  | var (idx : Nat)
  | sort (level : Nat)
  | const (name : Nat) (levels : Array Nat)
  | app (fn arg : Nat)
  | lam (name : Nat) (ty body : Nat)
  | pi (name : Nat) (ty body : Nat)
deriving Inhabited

inductive Decl where
  | def (name : Nat) (univParams : Array Nat) (type value : Nat)
  | ax (name : Nat) (univParams : Array Nat) (type : Nat)
  | ind (numParams : Nat) (univParams : Array Nat) (name : Nat) (type : Nat) (ctors : Array (Nat × Nat))
deriving Inhabited

structure State where
  names : Array Name := #[.anonymous]
  levels : Array Level := #[.zero]
  exprs : Array Expr := #[]
  decls : Array Decl := #[]
  imports : Array Name := #[]
  pendingInd : Option (Nat × Array Nat × Nat × Nat × Nat) := none
  pendingCtors : Array (Nat × Nat) := #[]

def barIdx (parts : Array String) : Nat :=
  parts.toList.findIdx (· == "|")

def parseLine (st : State) (parts : Array String) : State :=
  match parts[0]! with
  | "#DEF" =>
    let bi := barIdx parts
    let name := parts[1]!.toNat!
    let univParams := parts[2:bi].toArray.map (·.toNat!)
    let ty := parts[bi + 1]!.toNat!
    let val := parts[bi + 2]!.toNat!
    { st with decls := st.decls.push (.def name univParams ty val) }
  | "#AX" =>
    let bi := barIdx parts
    let name := parts[1]!.toNat!
    let univParams := parts[2:bi].toArray.map (·.toNat!)
    let ty := parts[bi + 1]!.toNat!
    { st with decls := st.decls.push (.ax name univParams ty) }
  | "#IND" =>
    let bi := barIdx parts
    let numParams := parts[1]!.toNat!
    let univParams := parts[2:bi].toArray.map (·.toNat!)
    let indName := parts[bi + 1]!.toNat!
    let indTy := parts[bi + 2]!.toNat!
    let numCtors := parts[bi + 3]!.toNat!
    if numCtors == 0 then
      { st with decls := st.decls.push (.ind numParams univParams indName indTy #[]) }
    else
      { st with pendingInd := some (numParams, univParams, indName, indTy, numCtors), pendingCtors := #[] }
  | "#INTRO" =>
    let ctorName := parts[1]!.toNat!
    let ctorTy := parts[2]!.toNat!
    let ctors := st.pendingCtors.push (ctorName, ctorTy)
    match st.pendingInd with
    | some (numParams, univParams, indName, indTy, expected) =>
      if expected <= ctors.size then
        { st with decls := st.decls.push (.ind numParams univParams indName indTy ctors),
                  pendingInd := none, pendingCtors := #[] }
      else
        { st with pendingCtors := ctors }
    | none => st
  | "#DI" =>
    let nameIdx := parts[1]!.toNat!
    { st with imports := st.imports.push st.names[nameIdx]! }
  | "#RI" =>
    let nameIdx := parts[2]!.toNat!
    { st with imports := st.imports.push st.names[nameIdx]! }
  | _ =>
    match parts[1]! with
    | "#NS" =>
      let s := if parts[3]! == "private" then "private_" else parts[3]!
      { st with names := st.names.push (st.names[parts[2]!.toNat!]!.str s) }
    | "#NI" => { st with names := st.names.push (st.names[parts[2]!.toNat!]!.str s!"n{parts[3]!}") }
    | "#US" => { st with levels := st.levels.push (.succ parts[2]!.toNat!) }
    | "#UM" => { st with levels := st.levels.push (.max parts[2]!.toNat! parts[3]!.toNat!) }
    | "#UP" => { st with levels := st.levels.push (.param parts[2]!.toNat!) }
    | "#EV" => { st with exprs := st.exprs.push (.var parts[2]!.toNat!) }
    | "#ES" => { st with exprs := st.exprs.push (.sort parts[2]!.toNat!) }
    | "#EC" => { st with exprs := st.exprs.push (.const parts[2]!.toNat! (parts[3:].toArray.map (·.toNat!))) }
    | "#EA" => { st with exprs := st.exprs.push (.app parts[2]!.toNat! parts[3]!.toNat!) }
    | "#EL" => { st with exprs := st.exprs.push (.lam parts[3]!.toNat! parts[4]!.toNat! parts[5]!.toNat!) }
    | "#EP" => { st with exprs := st.exprs.push (.pi parts[3]!.toNat! parts[4]!.toNat! parts[5]!.toNat!) }
    | _ => st

def parse (content : String) : State := Id.run do
  let mut st : State := {}
  for line in content.splitOn "\n" do
    let parts := line.splitOn " " |>.toArray
    if parts.size >= 2 then
      st := parseLine st parts
  st

section Render

variable (st : State)

partial def renderLevel (idx : Nat) : String :=
  match st.levels[idx]! with
  | .zero => "0"
  | .succ l => match st.levels[l]! with
    | .zero => "1"
    | _ => s!"{renderLevel l} + 1"
  | .max l₁ l₂ => s!"max {renderLevelAtom l₁} {renderLevelAtom l₂}"
  | .param n => toString (st.names[n]!)
where
  renderLevelAtom (idx : Nat) : String :=
    match st.levels[idx]! with
    | .zero => "0"
    | .param n => toString (st.names[n]!)
    | _ => s!"({renderLevel idx})"

def renderUnivParams (params : Array Nat) : String :=
  if params.isEmpty then ""
  else ".{" ++ ", ".intercalate (params.toList.map fun n => toString (st.names[n]!)) ++ "}"

def renderUnivArgs (args : Array Nat) : String :=
  if args.isEmpty then ""
  else ".{" ++ ", ".intercalate (args.toList.map (renderLevel st)) ++ "}"

partial def freshName (used : Array String) (hint : String) : String :=
  let hint := if hint.isEmpty || hint == "_" then "x" else hint
  if !used.contains hint then hint
  else
    let rec go (n : Nat) : String :=
      let candidate := s!"{hint}_{n}"
      if !used.contains candidate then candidate else go (n + 1)
    go 1

partial def varUsed (idx : Nat) (depth : Nat) : Bool :=
  match st.exprs[idx]! with
  | .var i => i == depth
  | .app fn arg => varUsed fn depth || varUsed arg depth
  | .lam _ ty body | .pi _ ty body => varUsed ty depth || varUsed body (depth + 1)
  | _ => false

partial def renderExpr (idx : Nat) (ctx : Array String := #[]) : String :=
  match st.exprs[idx]! with
  | .var i =>
    let dbIdx := ctx.size - 1 - i
    if dbIdx < ctx.size then ctx[dbIdx]! else s!"_var{i}"
  | .sort l =>
    let lvl := renderLevel st l
    match st.levels[l]! with
    | .zero | .param _ => s!"Type {lvl}"
    | _ => s!"Type ({lvl})"
  | .const n lvls => toString (st.names[n]!) ++ renderUnivArgs st lvls
  | .app fn arg =>
    let fnStr := renderExpr fn ctx
    let fnWrapped := match st.exprs[fn]! with
      | .lam .. | .pi .. => s!"({fnStr})"
      | _ => fnStr
    let argStr := renderExpr arg ctx
    let argWrapped := match st.exprs[arg]! with
      | .app .. | .lam .. | .pi .. => s!"({argStr})"
      | _ => argStr
    s!"{fnWrapped} {argWrapped}"
  | .lam n ty body =>
    let name := freshName ctx (toString (st.names[n]!))
    s!"fun ({name} : {renderExpr ty ctx}) => {renderExpr body (ctx.push name)}"
  | .pi n ty body =>
    let name := freshName ctx (toString (st.names[n]!))
    if varUsed st body 0 then
      s!"({name} : {renderExpr ty ctx}) → {renderExpr body (ctx.push name)}"
    else
      let tyStr := renderExpr ty ctx
      let tyWrapped := match st.exprs[ty]! with
        | .pi .. => s!"({tyStr})"
        | _ => tyStr
      s!"{tyWrapped} → {renderExpr body (ctx.push name)}"

def skipDecl (name : Name) : Bool :=
  match name with
  | .str _ s => s == "rec"
  | _ => false

def renderDecl (d : Decl) : Option String :=
  match d with
  | .def nameIdx univParams tyIdx valIdx =>
    let name := st.names[nameIdx]!
    if skipDecl name then none
    else some s!"def {name}{renderUnivParams st univParams} : {renderExpr st tyIdx} :=\n  {renderExpr st valIdx}"
  | .ax nameIdx univParams tyIdx =>
    let name := st.names[nameIdx]!
    some s!"axiom {name}{renderUnivParams st univParams} : {renderExpr st tyIdx}"
  | .ind numParams univParams nameIdx tyIdx ctors =>
    let name := st.names[nameIdx]!
    let (paramTele, indTy, ctx) := splitPi st numParams tyIdx #[]
    let header := s!"inductive {name}{renderUnivParams st univParams}{paramTele} : {renderExpr st indTy ctx} where"
    let ctorStrs := ctors.map fun (cn, ct) =>
      let shortName := match st.names[cn]! with
        | .str _ s => s
        | n => toString n
      s!"\n  | {shortName} : {renderExpr st (dropPi st numParams ct) ctx}"
    some (header ++ String.join ctorStrs.toList)
where
  splitPi (st : State) : Nat → Nat → Array String → String × Nat × Array String
    | 0, idx, ctx => ("", idx, ctx)
    | n + 1, idx, ctx => match st.exprs[idx]! with
      | .pi nameIdx ty body =>
        let name := freshName ctx (toString (st.names[nameIdx]!))
        let (rest, final, ctx') := splitPi st n body (ctx.push name)
        (s!" ({name} : {renderExpr st ty ctx})" ++ rest, final, ctx')
      | _ => ("", idx, ctx)
  dropPi (st : State) : Nat → Nat → Nat
    | 0, idx => idx
    | n + 1, idx => match st.exprs[idx]! with
      | .pi _ _ body => dropPi st n body
      | _ => idx

end Render

def convertFile (inputPath outputPath : String) : IO Unit := do
  let content ← IO.FS.readFile inputPath
  let st := parse content
  let mut output := ""
  for imp in st.imports do
    let impName := toString imp
    let lastPart := match imp with
      | .str _ s => s
      | _ => impName
    output := output ++ s!"import {lastPart}\n"
  if !st.imports.isEmpty then
    output := output ++ "\n"
  let mut count := 0
  for d in st.decls do
    if let some rendered := renderDecl st d then
      output := output ++ rendered ++ "\n\n"
      count := count + 1
  IO.FS.writeFile outputPath output
  println!"  {inputPath} → {outputPath} ({count} decls)"

def main (args : List String) : IO Unit := do
  let exportDir := args[0]!
  let outDir := args[1]!
  let entries ← System.FilePath.readDir exportDir
  for entry in entries do
    let path := entry.path
    if path.extension == some "txt" then
      let stem := path.fileStem.getD "unknown"
      let outPath := s!"{outDir}/{stem}.qdt"
      convertFile path.toString outPath
