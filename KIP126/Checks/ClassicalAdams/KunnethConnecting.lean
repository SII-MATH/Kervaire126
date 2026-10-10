import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Kunneth.Coaction.Proofs
import Lean.Elab.Command

/-! Audit the general homology comparison before specializing to an Adams
triangle. Künneth suspension compatibility is an explicit premise, not a
fixed axiom, and no Adams boundary formula is included in that premise. -/

open Lean Elab Command in
run_cmd do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in [``KIP126.Core.Algebra.gradedTensorLowerMap,
      ``KIP126.Core.Algebra.gradedTensorLowerMap_lof_tmul,
      ``KIP126.Core.Algebra.gradedTensorLowerMap_comp,
      ``KIP126.StableHomotopy.HoCofiberSequence.map,
      ``KIP126.StableHomotopy.HoCofiberSequence.map_comp,
      ``KIP126.StableHomotopy.connectingHomomorphism_map_comp,
      ``KIP126.StableHomotopy.connectingHomomorphism_map_naturality,
      ``KIP126.StableHomotopy.homotopyDesuspend,
      ``KIP126.StableHomotopy.Cohomology.mod2HomologyDesuspend,
      ``KIP126.StableHomotopy.Cohomology.mod2DoubleHomologyDesuspend,
      ``KIP126.StableHomotopy.Cohomology.mod2HomologyConnecting,
      ``KIP126.StableHomotopy.Cohomology.mod2HomologyConnecting_factor,
      ``KIP126.StableHomotopy.Cohomology.mod2HomologyConnecting_map_factor,
      ``KIP126.StableHomotopy.Cohomology.mod2CoactionMap_connecting,
      ``KIP126.StableHomotopy.Cohomology.mod2OuterUnitMap_connecting,
      ``KIP126.StableHomotopy.Cohomology.mod2Kunneth_connecting,
      ``KIP126.StableHomotopy.Cohomology.mod2TensorCoaction,
      ``KIP126.StableHomotopy.Cohomology.mod2TensorCoaction_counit,
      ``KIP126.StableHomotopy.Cohomology.mod2TensorCoaction_injective,
      ``KIP126.StableHomotopy.Cohomology.mod2TensorCoaction_naturality,
      ``KIP126.StableHomotopy.Cohomology.mod2TensorCoaction_connecting] do
    for a in ← liftCoreM (collectAxioms declaration) do
      unless allowed.contains a do
        throwError "unexpected Kunneth-boundary dependency: {declaration}: {a}"
  for m in (← getEnv).allImportedModuleNames do
    if (`KIP126.Mathlib).isPrefixOf m || (`KIPBase).isPrefixOf m ||
        (`Mathlib.Algebra.Homology.SpectralSequence).isPrefixOf m ||
        (`KIP126.Def.ClassicalAdams.MilnorCooperations).isPrefixOf m ||
        (`KIP126.Def.StageInput).isPrefixOf m ||
        (`KIP126.Def.ClassicalAdams.TowerPages).isPrefixOf m ||
        (`KIP126.Def.ClassicalAdams.TowerDifferential).isPrefixOf m ||
        (`KIP126.Def.ClassicalAdams.TowerHomology).isPrefixOf m ||
        (`KIP126.Def.ClassicalAdams.TowerResolution).isPrefixOf m ||
        (`KIP126.Def.Steenrod.MilnorCobar).isPrefixOf m ||
        (`KIP126.Def.AdamsE2).isPrefixOf m then
      throwError "unexpected below-page Kunneth-boundary import: {m}"

#print axioms KIP126.StableHomotopy.Cohomology.mod2Kunneth_connecting
#print axioms KIP126.StableHomotopy.Cohomology.mod2TensorCoaction_connecting
