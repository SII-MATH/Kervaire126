import KIP126.Interface.Solution.LinProgram.EtaNu
import Lean.Elab.Command

/-! Compiled-value checks for the fixed eta-nu deduction. The complete
low-filtration E2 calculation and generic tower argument are closed. The
fixed result explicitly retains `Def.standardSphereSeparated`, whose proof
is currently unfinished, as well as the fixed foundation and the supplied
literature vanishing result and sphere presentation. Equal axiom sets alone
do not establish that the separation obligation has been discharged. -/
namespace KIP126.Checks.LinEtaNu
open Lean Elab Command

private def freshModules : List Name :=
  [`KIP126.Def.ClassicalAdams.Detection.Vanishing,
    `KIP126.LinProgram.Certificates.StemFour,
    `KIP126.Interface.Solution.LinProgram.EtaNu]

private def forbiddenModules : List Name :=
  [`KIP126.Main,
    `KIP126.Interface.Challenge.Challenge2,
    `KIP126.Interface.Solution.Challenge2,
    `KIP126.Interface.Solution.LinProgram.Basis.Certification,
    `KIP126.Interface.Solution.LinProgram.Basis.Comparison,
    `KIP126.Interface.Solution.LinProgram.Multiplication,
    `KIP126.Interface.Solution.LinProgram.Differentials.VanishingD2,
    `KIP126.Interface.Solution.LinProgram.Staircase,
    `KIP126.Interface.Solution.LinProgram.Route.Certification,
    `KIP126.LinProgram.Tactic.LinE2]

private def forbiddenConstants : List Name :=
  [`KIP126.Main,
    `KIP126.Interface.Solution.challenge2,
    `KIP126.Interface.Solution.computationInterface,
    `KIP126.Interface.Solution.literatureInterface,
    `KIP126.Challenge2.ComputationInterface.results,
    `KIP126.Challenge2.ComputationResults,
    `KIP126.Computation.LinProofs.sphereTable_sound,
    `KIP126.Computation.LinProofs.differential_of_lookup,
    `KIP126.Interface.Solution.LinE2.basisTable_correct,
    `KIP126.Interface.Solution.sphereBasis,
    `KIP126.Interface.Solution.sphereMultiplicativeInterface,
    `KIP126.Interface.Solution.sphereStaircaseInterface,
    `KIP126.Interface.Solution.LinProgram.Route.certification]

private def declarationValue (name : Name) : CommandElabM Expr := do
  let env ← getEnv
  let some info := env.find? name | throwError "missing eta-nu declaration: {name}"
  let some value := info.value? (allowOpaque := true) |
    throwError "eta-nu declaration has no checkable compiled value: {name}"
  return value

/-- Accept a named projection or Lean's inlined structure projection. -/
private def hasProjection (value : Expr) (field structName : Name) (index : Nat) : Bool :=
  value.getUsedConstants.contains field ||
    (value.find? fun e => match e with
      | .proj name i _ => name == structName && i == index
      | _ => false).isSome

private def checkValueEdges (root : Name) (required : List Name) : CommandElabM Unit := do
  let value ← declarationValue root
  for dependency in required do
    unless value.getUsedConstants.contains dependency do
      throwError "eta-nu lost a direct compiled proof edge: {root}: {dependency}"

/-- Follow proof and definition values, including private helpers. A name
appearing only in a declaration's separate type is not enough. -/
private def checkValueClosure (root : Name) (required : List Name) : CommandElabM Unit := do
  let env ← getEnv
  let mut pending := #[root]
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    if name == `KIP126.Challenge2 || forbiddenConstants.any (·.isPrefixOf name) then
      throwError "eta-nu reads a consumer or total delivery: {root}: {name}"
    let some info := env.find? name | continue
    let owner := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx]!
      | none => name
    unless (`KIP126).isPrefixOf owner do continue
    if let some value := info.value? (allowOpaque := true) then
      if (value.find? fun e => match e with
          | .proj n i _ => n == `KIP126.Challenge2 ||
              (n == `KIP126.Challenge2.ComputationInterface && i == 1) ||
                n == `KIP126.Challenge2.ComputationResults
          | _ => false).isSome then
        throwError "eta-nu projects a consumer or total delivery: {root}: {name}"
      pending := pending ++ value.getUsedConstants
  for dependency in required do
    unless seen.contains dependency do
      throwError "eta-nu lost an explicit proof dependency: {root}: {dependency}"

open KIP126.Interface.Solution.LinProgram.EtaNu

run_cmd do
  let env ← getEnv
  for mod in env.allImportedModuleNames do
    if forbiddenModules.any (·.isPrefixOf mod) then
      throwError "eta-nu imports a consumer or total certification: {mod}"
  -- Scan every declaration owned by the three new modules, including private
  -- helpers, rather than comparing their already-collapsed `sorryAx` sets.
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless freshModules.contains env.header.moduleNames[idx]! do continue
    match info with
    | .axiomInfo _ => throwError "eta-nu introduces a project axiom: {name}"
    | _ => pure ()
    if let some value := info.value? (allowOpaque := true) then
      if value.getUsedConstants.contains ``sorryAx then
        throwError "eta-nu introduces a fresh direct placeholder: {name}"
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  for decl in [``KIP126.LinE2.StemFour.component_subsingleton,
      ``KIP126.Classical.Adams.TowerDetection.filtration_raise_of_pageTwo_subsingleton,
      ``KIP126.Classical.Adams.TowerDetection.mem_all_filtrations_of_pageTwo_zero,
      ``KIP126.Classical.Adams.TowerDetection.homotopy_eq_zero_of_pageTwo_zero_of_separated] do
    for ax in (← collectAxioms decl) do
      unless logical.contains ax do
        throwError "eta-nu data or generic tower lemma has an unexpected axiom: {decl}: {ax}"
  let modelAxioms ← collectAxioms ``KIP126.Classical.Adams.sphereAdamsModel
  let separationAxioms ← collectAxioms ``KIP126.Def.standardSphereSeparated
  for decl in [``pageTwo_stemFour_subsingleton, ``homotopy_four_zero, ``eta_nu_zero] do
    for ax in (← collectAxioms decl) do
      unless logical.contains ax || modelAxioms.contains ax || separationAxioms.contains ax do
        throwError "eta-nu has an axiom beyond the fixed model and named separation: {decl}: {ax}"
  let value ← declarationValue ``pageTwo_stemFour_subsingleton
  unless hasProjection value `KIP126.Challenge2.LiteratureResults.sphereVanishing
      `KIP126.Challenge2.LiteratureResults 2 do
    throwError "eta-nu no longer uses the supplied literature vanishing result"
  -- The comparison is now derived from one global map, not field zero.
  unless value.getUsedConstants.contains
      ``KIP126.Classical.Adams.LinE2Presentation.comparison do
    throwError "eta-nu no longer uses the derived presentation comparison"
  checkValueEdges ``pageTwo_stemFour_subsingleton
    [``KIP126.LinE2.StemFour.component_subsingleton]
  checkValueEdges ``homotopy_four_zero
    [``pageTwo_stemFour_subsingleton,
      ``KIP126.Classical.Adams.TowerDetection.homotopy_eq_zero_of_pageTwo_zero_of_separated,
      ``KIP126.Def.standardSphereSeparated]
  checkValueEdges ``eta_nu_zero [``homotopy_four_zero]
  checkValueClosure ``eta_nu_zero
    [``KIP126.LinE2.StemFour.component_subsingleton,
      ``KIP126.Classical.Adams.TowerDetection.homotopy_eq_zero_of_pageTwo_zero_of_separated,
      ``KIP126.Def.standardSphereSeparated]

end KIP126.Checks.LinEtaNu

-- This named unfinished dependency must remain visible independently of
-- the foundation's identical `sorryAx` entry.
#print axioms KIP126.Def.standardSphereSeparated
#print axioms KIP126.Interface.Solution.LinProgram.EtaNu.eta_nu_zero
