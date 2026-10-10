import KIP126.Def.ClassicalAdams.TowerHomology.Splitting.Proofs
import Lean.Elab.Command

/-! The coface identities and normalized splitting must come from the actual
unit, multiplication, and exact triangle, without page-coordinate assumptions. -/

open Lean Elab Command in
run_cmd do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in [``KIP126.StableHomotopy.Cohomology.mod2Coaction,
      ``KIP126.StableHomotopy.Cohomology.mod2CoactionMap,
      ``KIP126.StableHomotopy.Cohomology.mod2AdamsUnit_naturality,
      ``KIP126.StableHomotopy.Cohomology.mod2Coaction_naturality,
      ``KIP126.StableHomotopy.Cohomology.mod2Coaction_coface,
      ``KIP126.StableHomotopy.Cohomology.mod2Coaction_counit,
      ``KIP126.StableHomotopy.Cohomology.mod2FreeAction_naturality,
      ``KIP126.StableHomotopy.Cohomology.mod2Coaction_coefficient,
      ``KIP126.StableHomotopy.Cohomology.cooperationDiagonal_counit_left,
      ``KIP126.StableHomotopy.Cohomology.cooperationDiagonal_counit_right,
      ``KIP126.StableHomotopy.Cohomology.mod2CoactionMap_naturality,
      ``KIP126.StableHomotopy.Cohomology.mod2CoactionMap_coface,
      ``KIP126.Classical.Adams.adamsHomologyUnit_eq_coaction,
      ``KIP126.Classical.Adams.adamsHomologyUnit_naturality,
      ``KIP126.Classical.Adams.adamsHomologyAction_naturality,
      ``KIP126.Classical.Adams.adamsHomologyNormalize,
      ``KIP126.Classical.Adams.adamsHomologyNormalize_apply,
      ``KIP126.Classical.Adams.adamsHomologyNormalize_action,
      ``KIP126.Classical.Adams.adamsHomologyNormalize_unit,
      ``KIP126.Classical.Adams.adamsHomologyNormalize_eq_self,
      ``KIP126.Classical.Adams.adamsHomologyNormalize_idempotent,
      ``KIP126.Classical.Adams.adamsHomologyNormalize_naturality,
      ``KIP126.Classical.Adams.adamsHomologyNormalize_range,
      ``KIP126.Classical.Adams.adamsHomologyNormalize_ker,
      ``KIP126.Classical.Adams.adamsHomologyBoundary_normalize,
      ``KIP126.Classical.Adams.adamsHomologySplitEquiv,
      ``KIP126.Classical.Adams.adamsHomologySplitEquiv_apply,
      ``KIP126.Classical.Adams.adamsHomologySplitEquiv_symm_apply] do
    for a in ← liftCoreM (collectAxioms declaration) do
      unless allowed.contains a do
        throwError "unexpected coaction/splitting dependency: {declaration}: {a}"
  for m in (← getEnv).allImportedModuleNames do
    if (`KIP126.Mathlib).isPrefixOf m || (`KIPBase).isPrefixOf m ||
        (`Mathlib.Algebra.Homology.SpectralSequence).isPrefixOf m ||
        (`KIP126.Def.ClassicalAdams.MilnorCooperations).isPrefixOf m ||
        (`KIP126.Def.StageInput).isPrefixOf m ||
        (`KIP126.Def.AdamsE2).isPrefixOf m then
      throwError "unexpected coaction/splitting import: {m}"

/- The decomposition applies to every actual stage, with the next stage
definitionally the fiber in the constructed splitting. -/
open CategoryTheory MonoidalCategory KIP126.Classical.Adams KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology in
noncomputable example {C : Type*} [StableHomotopyCategory C]
    [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C))
    [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]
    (R : Mod2RingStructure H) (X : C) (s : ℕ) (n : ℤ) :
    Mod2Homology H n (H.HF2 ⊗ adamsTower H.unit X s) ≃ₗ[ℤ]
      Mod2Homology H n (adamsTower H.unit X s) ×
        Mod2Homology H (n - 1) (adamsTower H.unit X (s + 1)) :=
  adamsHomologySplitEquiv H R (adamsTower H.unit X s) n

#print axioms KIP126.StableHomotopy.Cohomology.mod2Coaction_coface
#print axioms KIP126.Classical.Adams.adamsHomologyNormalize_naturality
#print axioms KIP126.Classical.Adams.adamsHomologySplitEquiv
