import Lean

/-!
Compiled-environment audit of the canonical library's proof dependencies.
The single development-only project input is declared under `KIP126.Main.Axiom`
(see PROJECT_BOUNDARY.md);
they are inventoried separately from `sorryAx` and remain failures of this
strict, final-acceptance audit. The initializer substitutes the source root.
-/

open Lean

def auditedRoot : Name := `KIP126
def auditedDirectory : System.FilePath := "KIP126"
def rootLeanFile : System.FilePath := "KIP126.lean"

def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def withImportedEnv {α} (modules : Array Name) (act : CoreM α) : IO α := do
  initSearchPath (← findSysroot)
  unsafe Lean.withImportModules (modules.map (fun moduleName => { module := moduleName })) {}
    (trustLevel := 1024) fun env =>
      Prod.fst <$> Core.CoreM.toIO act
        (ctx := { fileName := "<axioms>", fileMap := default }) (s := { env := env })

def inAuditedLib (moduleName : Name) : Bool :=
  moduleName == auditedRoot || auditedRoot.isPrefixOf moduleName

def pathToModule (path : System.FilePath) : Name :=
  (path.withExtension "").components.foldl (fun name component => Name.mkStr name component)
    Name.anonymous

partial def collectLeanModules (directory : System.FilePath) : IO (Array Name) := do
  let mut modules := #[]
  for entry in (← directory.readDir) do
    if (← entry.path.isDir) then
      modules := modules ++ (← collectLeanModules entry.path)
    else if entry.path.extension == some "lean" then
      modules := modules.push (pathToModule entry.path)
  return modules

def auditedModules : IO (Array Name) := do
  let modules ← collectLeanModules auditedDirectory
  if (← rootLeanFile.pathExists) then
    return #[auditedRoot] ++ modules
  return modules

abbrev AxiomCacheM := ReaderT Environment (StateM (Lean.NameMap Bool))

partial def reachesDisallowedAxiom (constantName : Name) : AxiomCacheM Bool := do
  if let some result := (← get).find? constantName then
    return result
  modify (·.insert constantName false)
  let env ← read
  let anyExpr (expressions : Array Expr) : AxiomCacheM Bool :=
    expressions.anyM fun expression => expression.getUsedConstants.anyM reachesDisallowedAxiom
  let result ← match env.checked.get.find? constantName with
    | some (.axiomInfo value) =>
        if !allowedAxioms.contains constantName then pure true else anyExpr #[value.type]
    | some (.defnInfo value) => anyExpr #[value.type, value.value]
    | some (.thmInfo value) => anyExpr #[value.type, value.value]
    | some (.opaqueInfo value) => anyExpr #[value.type, value.value]
    | some (.quotInfo _) => pure false
    | some (.ctorInfo value) => anyExpr #[value.type]
    | some (.recInfo value) => anyExpr #[value.type]
    | some (.inductInfo value) =>
        if (← anyExpr #[value.type]) then pure true else value.ctors.anyM reachesDisallowedAxiom
    | none => pure false
  modify (·.insert constantName result)
  return result

def owningModule? (env : Environment) (moduleNames : Array Name)
    (declarationName : Name) : Option Name := do
  let index ← env.getModuleIdxFor? declarationName
  moduleNames[index.toNat]?

structure AuditReport where
  audited : Nat := 0
  registered : Array String := #[]
  sorryDependents : Array String := #[]
  projectDependents : Array String := #[]
  errors : Array String := #[]

def audit : CoreM AuditReport := do
  let env ← getEnv
  let moduleNames := env.allImportedModuleNames
  -- The historical migration has explicitly retained assumptions. Even a clean
  -- declaration must be ported into the canonical model before KIP126 imports it.
  if moduleNames.any (fun n => n == `KIPBase || (`KIPBase).isPrefixOf n) then
    return { errors := #["KIP126 imports the isolated KIPBase historical component"] }
  let candidates : Array Name := env.constants.fold (init := #[]) fun declarations declarationName _ =>
    match owningModule? env moduleNames declarationName with
    | some moduleName =>
        if inAuditedLib moduleName then declarations.push declarationName else declarations
    | none => declarations
  let candidates := candidates.qsort (fun a b => a.toString < b.toString)
  let projectAxioms := candidates.filter fun name =>
    match env.checked.get.find? name with
    | some (.axiomInfo _) => !allowedAxioms.contains name
    | _ => false
  let mut report : AuditReport := { audited := candidates.size }
  for name in projectAxioms do
    let some moduleName := owningModule? env moduleNames name
      | continue
    -- Stage assumptions are centralized; registration still fails the strict
    -- completion audit below and never grants foundational trust.
    if name == `KIP126.Main.Axiom.challenge2 && moduleName == `KIP126.Main.Axiom.Challenge2 then
      let line := s!"  {name} (declared in {moduleName})"
      report := { report with registered := report.registered.push line }
    else
      let line := s!"project axiom {name} is declared in {moduleName}, outside the single project-input boundary"
      report := { report with errors := report.errors.push line }
  let offenders : Array Name :=
    (candidates.filterM reachesDisallowedAxiom |>.run env).run' {}
  for declarationName in offenders do
    let axioms ← collectAxioms declarationName
    let disallowed := axioms.filter fun axiomName => !allowedAxioms.contains axiomName
    let sorryDeps := disallowed.filter (· == ``sorryAx)
    let project := disallowed.filter projectAxioms.contains
    let unexpected := disallowed.filter fun name =>
      name != ``sorryAx && !projectAxioms.contains name
    if !sorryDeps.isEmpty then
      let line := s!"  {declarationName} → {sorryDeps.toList}"
      report := { report with sorryDependents := report.sorryDependents.push line }
    if !project.isEmpty then
      let line := s!"  {declarationName} → {project.toList}"
      report := { report with projectDependents := report.projectDependents.push line }
    if !unexpected.isEmpty then
      let line := s!"  {declarationName} → unexpected axioms {unexpected.toList}"
      report := { report with errors := report.errors.push line }
  return report

def main : IO UInt32 := do
  let modules ← auditedModules
  if modules.isEmpty then
    IO.eprintln s!"axioms: found no Lean modules under {auditedDirectory}: the audit is miswired."
    return 1
  let report ← withImportedEnv modules audit
  if report.audited == 0 && !report.errors.isEmpty then
    for message in report.errors do
      IO.eprintln message
    return 1
  if report.audited == 0 then
    IO.eprintln s!"axioms: audited 0 declarations in {auditedRoot}: the audit is miswired."
    return 1
  IO.println s!"axioms: audited {report.audited} {auditedRoot} declaration(s)."
  if !report.registered.isEmpty then
    IO.println s!"project axioms in stage Axiom directories ({report.registered.size}):"
    for line in report.registered do IO.println line
  if !report.projectDependents.isEmpty then
    IO.println s!"project-axiom dependency cone ({report.projectDependents.size} declarations):"
    for line in report.projectDependents do IO.println line
  if !report.sorryDependents.isEmpty then
    IO.println s!"sorryAx dependency cone ({report.sorryDependents.size} declarations):"
    for line in report.sorryDependents do IO.println line
  if !report.errors.isEmpty then
    IO.eprintln s!"unexpected or misplaced axioms ({report.errors.size}):"
    for line in report.errors do IO.eprintln line
    IO.println "AXIOM_AUDIT_ERROR=1"
    return 1
  if report.registered.isEmpty && report.projectDependents.isEmpty &&
      report.sorryDependents.isEmpty then
    IO.println s!"axioms: all dependencies within the foundational allowlist {allowedAxioms}."
    return 0
  if !report.registered.isEmpty || !report.projectDependents.isEmpty then
    IO.println "AXIOM_AUDIT_PROJECT=1"
  if !report.sorryDependents.isEmpty then IO.println "AXIOM_AUDIT_SORRY=1"
  IO.println "AXIOM_AUDIT_DEBT=1"
  return 1
