module

public import KIP126.Interface.Solution.LinProgram.Naturality.Row245131
public import Lean.Elab.Command

@[expose] public section


/-! A replay on the fixed η cofiber and its actual top-cell map. The native
output stays conditional on the source equation and actual map coordinates.
The universal double-desuspension law is now derived from the actual tower
squares. Fixed-model foundational `sorryAx` dependencies are inherited and
reported; this check does not certify the remaining instance obligations. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in env.allImportedModuleNames do
    if (`KIP126.Main).isPrefixOf mod ||
        mod == `KIP126.Interface.Solution.Challenge2 ||
        mod == `KIP126.Interface.Solution.LinProgram.Basis.Certification ||
        mod == `KIP126.Interface.Solution.LinProgram.Multiplication ||
        mod == `KIP126.Interface.Solution.LinProgram.Differentials.VanishingD2 ||
        mod == `KIP126.Interface.Solution.LinProgram.Staircase ||
        mod == `KIP126.Interface.Solution.LinProgram.Route.Certification then
      throwError "naturality replay imported a consumer or aggregate certification: {mod}"
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  for decl in [``KIP126.Computation.LinProofs.Raw.Naturality.output245131_in_export,
      ``KIP126.Computation.LinProofs.Raw.Naturality.native_source_degree_shift,
      ``KIP126.Classical.Adams.adamsInternalE2Induced_hasDifferential,
      ``KIP126.Classical.Adams.Suspension.TowerComparison.hasDifferential_desuspendTwice] do
    for ax in (← collectAxioms decl) do
      unless logical.contains ax do
        throwError "unexpected axiom in native transcription or generic naturality {decl}: {ax}"
  let modelAxioms ← collectAxioms ``KIP126.Classical.Adams.sphereAdamsModel
  for decl in [``KIP126.Interface.Solution.LinProgram.Naturality.row245130_topCell,
      ``KIP126.Interface.Solution.LinProgram.Naturality.row245131,
      ``KIP126.Interface.Solution.LinProgram.Naturality.doubleDesuspensionCompatible,
      ``KIP126.Interface.Solution.LinProgram.Naturality.row245131_native] do
    for ax in (← collectAxioms decl) do
      unless logical.contains ax || modelAxioms.contains ax do
        throwError "naturality replay adds an axiom beyond the fixed Def model: {decl}: {ax}"

open KIP126.Computation.LinProofs.Raw.Naturality in
example : output245131 = ⟨245131, "N", 2, 17, 3, [0], [0]⟩ := rfl

open KIP126.Computation.LinProofs.Raw.Naturality in
example : sourceCandidate245130 =
    ⟨245130, some 0, some "D", some "Ceta", some 17, some 2,
      some 19, some 3, some "0", some "0", none⟩ := rfl

open KIP126.Computation.LinProofs.Raw.Naturality in
example : target245131 =
    ⟨245131, some 0, some "N", some "S0", some 15, some 2,
      some 17, some 3, some "0", some "0", some "Ceta__S0"⟩ := rfl

open KIP126.Computation.LinProofs.Raw.Naturality in
example : mapSuspension = 2 := rfl

#print axioms KIP126.Classical.Adams.adamsInternalE2Induced_hasDifferential
#print axioms KIP126.Interface.Solution.LinProgram.Naturality.row245130_topCell
#print axioms KIP126.Interface.Solution.LinProgram.Naturality.row245131

#print axioms KIP126.Interface.Solution.LinProgram.Naturality.row245131_native
