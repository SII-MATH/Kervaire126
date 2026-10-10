import KIP126.Def.ClassicalAdams.TowerHomology.Normalized.Proofs
import Lean.Elab.Command

/-! Derive normalized coefficient homology from a ring and tensor exactness.
All structural data remain parameters. No first-page coordinate, fixed
foundation, computation table, or spectral-sequence adapter may enter. -/

open Lean Elab Command in
run_cmd do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in [``KIP126.Classical.Adams.adamsResolutionTriangle,
      ``KIP126.Classical.Adams.adamsResolutionTriangle_distinguished,
      ``KIP126.Classical.Adams.adamsHomologySequence,
      ``KIP126.Classical.Adams.adamsHomologyUnit,
      ``KIP126.Classical.Adams.adamsHomologyAction,
      ``KIP126.Classical.Adams.adamsHomologyBoundary,
      ``KIP126.Classical.Adams.adamsHomologyAction_unit,
      ``KIP126.Classical.Adams.adamsHomologyUnit_injective,
      ``KIP126.Classical.Adams.adamsHomologyBoundary_exact,
      ``KIP126.Classical.Adams.adamsHomologyBoundary_surjective,
      ``KIP126.Classical.Adams.adamsHomologyBoundary_ker,
      ``KIP126.Classical.Adams.adamsHomologyBoundary_ker_action_bijective,
      ``KIP126.Classical.Adams.adamsHomologyKernelEquiv,
      ``KIP126.Classical.Adams.adamsHomologyKernelEquiv_apply,
      ``KIP126.Classical.Adams.adamsHomologyKernelEquiv_symm_boundary,
      ``KIP126.Classical.Adams.adamsHomologyQuotientEquiv,
      ``KIP126.Classical.Adams.adamsHomologyQuotientEquiv_mkQ,
      ``KIP126.Classical.Adams.sphereCoefficientHomologyEquiv,
      ``KIP126.Classical.Adams.sphereCoefficientHomologyEquiv_map_ker,
      ``KIP126.Classical.Adams.sphereFirstTowerHomologyEquiv,
      ``KIP126.Classical.Adams.sphereFirstTowerHomologyEquiv_boundary,
      ``KIP126.Classical.Adams.sphereFirstPageFiltrationOneEquiv] do
    for a in ← liftCoreM (collectAxioms declaration) do
      unless allowed.contains a do
        throwError "unexpected normalized tower-homology dependency: {declaration}: {a}"
  for m in (← getEnv).allImportedModuleNames do
    if (`KIP126.Mathlib).isPrefixOf m || (`KIPBase).isPrefixOf m ||
        (`Mathlib.Algebra.Homology.SpectralSequence).isPrefixOf m ||
        (`KIP126.Def.ClassicalAdams.MilnorCooperations).isPrefixOf m ||
        (`KIP126.Def.StageInput).isPrefixOf m ||
        (`KIP126.Def.AdamsE2).isPrefixOf m then
      throwError "unexpected normalized tower-homology import: {m}"

open CategoryTheory CategoryTheory.MonoidalCategory KIP126.Classical.Adams
  KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology in
noncomputable example {C : Type*} [StableHomotopyCategory C]
    [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C))
    [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]
    (R : Mod2RingStructure H) (X : C) (s : ℕ) (n : ℤ) :
    LinearMap.ker (adamsHomologyAction H R (adamsTower H.unit X s) n) ≃ₗ[ℤ]
      Mod2Homology H (n - 1) (adamsTower H.unit X (s + 1)) :=
  adamsHomologyKernelEquiv H R (adamsTower H.unit X s) n

#print axioms KIP126.Classical.Adams.adamsHomologyKernelEquiv
#print axioms KIP126.Classical.Adams.adamsHomologyQuotientEquiv
#print axioms KIP126.Classical.Adams.sphereFirstPageFiltrationOneEquiv
