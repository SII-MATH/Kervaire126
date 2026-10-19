module

public import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Sphere.Stage.Comparison.Proofs
public import Lean.Elab.Command

@[expose] public section


/-! Generic comparison only: zero long connecting maps are not arbitrary
finite-page cycles, and no total pairing or actual Lin comparison is asserted. -/
open KIP126.Classical.Adams.LongLayerStageComparison
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in env.allImportedModuleNames do
    if (`KIP126.Interface).isPrefixOf mod || (`KIP126.Main).isPrefixOf mod ||
        (`KIP126.LinProgram).isPrefixOf mod || (`KIP126.Def.StageInput).isPrefixOf mod then
      throwError "generic stage comparison imports an actual model or delivery: {mod}"
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  for decl in [``projectionNat, ``projectionNat_ι, ``projectionNat_eq,
      ``stageProjected, ``coefficientAction, ``stageProjected_eq_actual,
      ``stageProjected_ι, ``coefficientAction_ι, ``defect_factors,
      ``eq_on_representatives, ``actual_eq_on_representatives] do
    for ax in (← collectAxioms decl) do
      unless logical.contains ax do throwError "unexpected stage comparison axiom {decl}: {ax}"

#print axioms KIP126.Classical.Adams.LongLayerStageComparison.defect_factors
#print axioms KIP126.Classical.Adams.LongLayerStageComparison.actual_eq_on_representatives
