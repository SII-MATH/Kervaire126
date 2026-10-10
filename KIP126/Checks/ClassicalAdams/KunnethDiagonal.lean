import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Kunneth.Diagonal.Proofs
import Lean.Elab.Command

/-! The actual tensor diagonal and conditional coassociativity use no Adams
page, fixed foundation, Milnor formula, Lin comparison, or project axiom. -/

open Lean Elab Command in
run_cmd do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in [``KIP126.Core.Algebra.gradedTensorAssoc,
      ``KIP126.Core.Algebra.gradedTensorAssoc_lof_tmul,
      ``KIP126.StableHomotopy.Cohomology.cooperationTensorMap_comp,
      ``KIP126.StableHomotopy.Cohomology.cooperationTensorDiagonal,
      ``KIP126.StableHomotopy.Cohomology.cooperationTensorComultiply,
      ``KIP126.StableHomotopy.Cohomology.Mod2KunnethDiagonalCompatible,
      ``KIP126.StableHomotopy.Cohomology.cooperationTensorDiagonal_apply,
      ``KIP126.StableHomotopy.Cohomology.cooperationTensorDiagonal_counit,
      ``KIP126.StableHomotopy.Cohomology.mod2TensorCoaction_coassoc,
      ``KIP126.StableHomotopy.Cohomology.cooperationTensorDiagonal_coassoc] do
    for a in ← liftCoreM (collectAxioms declaration) do
      unless allowed.contains a do
        throwError "unexpected Kunneth-diagonal dependency: {declaration}: {a}"
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
      throwError "unexpected below-page Kunneth-diagonal import: {m}"

#print axioms KIP126.StableHomotopy.Cohomology.mod2TensorCoaction_coassoc
#print axioms KIP126.StableHomotopy.Cohomology.cooperationTensorDiagonal_coassoc
