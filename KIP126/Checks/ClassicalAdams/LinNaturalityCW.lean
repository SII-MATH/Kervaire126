import KIP126.Interface.Solution.LinProgram.Naturality.CWToCeta
import Lean.Elab.Command

/-! This audit intentionally uses non-module imports so that Lean loads proof
bodies and private helpers throughout the dependency closure. Public module
imports alone omit those values and would leave the audit incomplete. -/




/-! These are checks of the conditional producer's compiled dependencies.
They do not discharge hzero, the CW source equation, or any native coordinate
comparison. Foundational axioms may only be inherited from the same fixed model. -/
namespace KIP126.Checks.LinNaturalityCW
open Lean Elab Command

private def forbiddenModules : List Name :=
  [`KIP126.Main,
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

/-- Traverse compiled proof/definition values, including projections that Lean
has inlined. Merely containing a delivery's type is not a proof dependency. -/
private def checkValueClosure (root : Name) (required : List Name) : CommandElabM Unit := do
  let env ← getEnv
  let mut pending := #[root]
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    if forbiddenConstants.any (·.isPrefixOf name) then
      throwError "CW naturality reads a total computation result: {root}: {name}"
    let some info := env.find? name | continue
    -- Private helper names start with `_private`; their defining module,
    -- rather than the declaration namespace, determines project ownership.
    let owner := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx]!
      | none => name
    unless (`KIP126).isPrefixOf owner do continue
    if let some value := info.value? (allowOpaque := true) then
      if (owner == `KIP126.Interface.Solution.LinProgram.Naturality.CWToCeta ||
          owner == `KIP126.Interface.Solution.LinProgram.Naturality.CWModel) &&
          value.getUsedConstants.contains ``sorryAx then
        throwError "CW replay introduces a fresh placeholder: {root}: {name}"
      if (value.find? fun e => match e with
          | .proj n i _ =>
              (n == `KIP126.Challenge2.ComputationInterface && i == 1) ||
                n == `KIP126.Challenge2.ComputationResults
          | _ => false).isSome then
        throwError "CW naturality projects a total computation result: {root}: {name}"
      pending := pending ++ value.getUsedConstants
  for dependency in required do
    unless seen.contains dependency do
      throwError "CW naturality lost its actual transfer: {root}: {dependency}"

/-- Require an edge in the compiled value, rather than accepting a name that
only occurs in the separate declaration type or elsewhere in the environment. -/
private def checkValueEdges (root : Name) (required : List Name) : CommandElabM Unit := do
  let env ← getEnv
  let some info := env.find? root | throwError "missing CW declaration: {root}"
  let some value := info.value? (allowOpaque := true) |
    throwError "CW declaration has no checkable compiled value: {root}"
  for dependency in required do
    unless value.getUsedConstants.contains dependency do
      throwError "CW declaration lost a direct construction dependency: {root}: {dependency}"

open KIP126.Interface.Solution.LinProgram.NaturalityCW
open KIP126.Classical.Adams.Suspension.Fourfold

run_cmd do
  let env ← getEnv
  for mod in env.allImportedModuleNames do
    if forbiddenModules.any (·.isPrefixOf mod) then
      throwError "CW naturality imported a consumer or total certification: {mod}"
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  for decl in [``KIP126.Computation.LinProofs.Raw.NaturalityHighStem.source462479Full,
      ``KIP126.Computation.LinProofs.Raw.NaturalityHighStem.native_cw_degree_shift,
      ``desuspendFourInternalPage_hasDifferential] do
    for ax in (← collectAxioms decl) do
      unless logical.contains ax do
        throwError "unexpected axiom in native transcription or generic transfer {decl}: {ax}"
  let modelAxioms ← collectAxioms ``KIP126.Classical.Adams.sphereAdamsModel
  for decl in [``extension, ``extension_spec, ``CW, ``q, ``fixed_triangles,
      ``toQuadCeta, ``cetaDesuspendFour, ``cetaDesuspendFour_hasDifferential,
      ``cwToCetaE2, ``cwToCetaE2_hasDifferential, ``row462480, ``row462481_from_cw,
      ``row462481_from_literature] do
    for ax in (← collectAxioms decl) do
      unless logical.contains ax || modelAxioms.contains ax do
        throwError "CW naturality adds an axiom beyond the fixed Def model: {decl}: {ax}"
  for root in [``row462480, ``row462481_from_cw] do
    checkValueClosure root [``cwToCetaE2_hasDifferential, ``cwToCetaE2,
      ``cetaDesuspendFour_hasDifferential, ``cetaDesuspendFour, ``toQuadCeta, ``q,
      ``desuspendFourInternalPage_hasDifferential,
      ``KIP126.Classical.Adams.adamsInternalE2Induced_hasDifferential]
  checkValueClosure ``row462481_from_literature
    [``row462481_from_cw,
      ``KIP126.Interface.Solution.LinProgram.EtaNu.eta_nu_zero,
      ``KIP126.Interface.Solution.LinProgram.EtaNu.homotopy_four_zero,
      ``KIP126.Def.standardSphereSeparated]
  checkValueEdges ``row462481_from_literature
    [``row462481_from_cw, ``KIP126.Interface.Solution.LinProgram.EtaNu.eta_nu_zero]
  checkValueEdges ``row462480 [``cwToCetaE2_hasDifferential]
  checkValueEdges ``row462481_from_cw [``row462480,
    ``KIP126.Interface.Solution.LinProgram.NaturalityHighStem.row462481]
  checkValueEdges ``cwToCetaE2 [``cetaDesuspendFour, ``toQuadCeta,
    ``KIP126.Classical.Adams.adamsInternalE2Induced]
  checkValueEdges ``cwToCetaE2_hasDifferential [``cetaDesuspendFour_hasDifferential,
    ``KIP126.Classical.Adams.adamsInternalE2Induced_hasDifferential]
  checkValueEdges ``cetaDesuspendFour [``desuspendFourInternalPage,
    ``KIP126.Interface.Solution.LinProgram.Naturality.cetaTowerComparison,
    ``KIP126.Interface.Solution.LinProgram.Naturality.cetaShiftTowerComparison]
  checkValueEdges ``cetaDesuspendFour_hasDifferential
    [``desuspendFourInternalPage_hasDifferential]
  checkValueEdges ``toQuadCeta [``q, ``quadShiftIso]

end KIP126.Checks.LinNaturalityCW

open KIP126.Computation.LinProofs.Raw.NaturalityHighStem in
example : source462479Full =
    ⟨462479, some 0, some "D", some "CW_nu_eta", some 129, some 15,
      some 144, some 3, some "1", some "0", none⟩ := rfl

open KIP126.Computation.LinProofs.Raw.NaturalityHighStem in
example : cwMapSuspension = 4 := rfl

#print axioms KIP126.Interface.Solution.LinProgram.NaturalityCW.row462480
#print axioms KIP126.Interface.Solution.LinProgram.NaturalityCW.row462481_from_cw

#print axioms KIP126.Interface.Solution.LinProgram.NaturalityCW.row462481_from_literature
