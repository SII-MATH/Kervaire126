import KIP126.Def.ClassicalAdams.TowerHomology.Kunneth.Iterated.Proofs
import Lean.Elab.Command

/-! Audit the derivation from explicitly parameterized, homology-level Künneth.
The input has no Adams pages, differentials, or permanence claims. No value
for the fixed sphere foundation, Milnor coordinates, or Lin data is imported. -/

open Lean Elab Command in
run_cmd do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in [``KIP126.Core.Algebra.rTensor_kernel_range,
      ``KIP126.Core.Algebra.directSum_kernel_range,
      ``KIP126.Core.Algebra.directSumConcentratedEquiv,
      ``KIP126.Core.Algebra.rTensorKernelEquiv,
      ``KIP126.Core.Algebra.directSumKernelEquiv,
      ``KIP126.Core.Algebra.gradedTensorKernelEquiv,
      ``KIP126.Core.Algebra.gradedTensorKernelEquiv_coe,
      ``KIP126.Core.Algebra.gradedTensorMap_lof_tmul,
      ``KIP126.StableHomotopy.Cohomology.reducedCooperationTensorEquiv,
      ``KIP126.StableHomotopy.Cohomology.reducedCooperationTensorEquiv_coe,
      ``KIP126.StableHomotopy.Cohomology.coefficientTensorEquiv,
      ``KIP126.StableHomotopy.Cohomology.coefficientTensorEquiv_zero_tmul,
      ``KIP126.StableHomotopy.Cohomology.cooperationCounitF2_eq_zero_of_ne,
      ``KIP126.StableHomotopy.Cohomology.cooperationTensorAugmentation_ker,
      ``KIP126.StableHomotopy.Cohomology.reducedCooperationAugmentationEquiv,
      ``KIP126.StableHomotopy.Cohomology.reducedCooperationTensorInclusion_symm,
      ``KIP126.StableHomotopy.Cohomology.reducedCooperationTensorCongr,
      ``KIP126.StableHomotopy.Cohomology.iteratedReducedCooperations,
      ``KIP126.Classical.Adams.adamsHomologyKunneth_map_ker,
      ``KIP126.Classical.Adams.adamsHomologyKunnethKernelEquiv,
      ``KIP126.Classical.Adams.adamsNextHomologyTensorEquiv,
      ``KIP126.Classical.Adams.adamsNextHomologyTensorEquiv_boundary,
      ``KIP126.Classical.Adams.adamsTowerHomologyTensorEquiv,
      ``KIP126.Classical.Adams.adamsTowerHomologyIteratedEquiv,
      ``KIP126.Classical.Adams.adamsTowerHomologyIteratedEquiv_zero,
      ``KIP126.Classical.Adams.adamsTowerHomologyIteratedEquiv_succ,
      ``KIP126.Classical.Adams.adamsFirstPageIteratedEquiv,
      ``KIP126.Classical.Adams.adamsFirstPageIteratedEquiv_apply] do
    for a in ← liftCoreM (collectAxioms declaration) do
      unless allowed.contains a do
        throwError "unexpected Kunneth-recurrence dependency: {declaration}: {a}"
  for m in (← getEnv).allImportedModuleNames do
    if (`KIP126.Mathlib).isPrefixOf m || (`KIPBase).isPrefixOf m ||
        (`Mathlib.Algebra.Homology.SpectralSequence).isPrefixOf m ||
        (`KIP126.Def.ClassicalAdams.MilnorCooperations).isPrefixOf m ||
        (`KIP126.Def.StageInput).isPrefixOf m ||
        (`KIP126.Def.AdamsE2).isPrefixOf m then
      throwError "unexpected Kunneth-recurrence import: {m}"

/- This is an all-filtration statement about the actual sphere quotient page,
conditional on the lower-level input. It does not supply that input by axiom. -/
open CategoryTheory MonoidalCategory KIP126.Classical.Adams KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology in
noncomputable example {C : Type*} [StableHomotopyCategory C] [MonoidalPreadditive C]
    [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C))
    (R : Mod2RingStructure H) (K : Mod2CooperationKunneth H R)
    [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]
    (s : ℕ) (t : ℤ) :
    letI := adamsPageF2Module H R SphereSpectrum 1 le_rfl s t
    adamsPage H.unit SphereSpectrum 1 le_rfl s t ≃ₗ[ZMod 2]
      iteratedReducedCooperations H R (fun i => mod2HomologyF2 H R i SphereSpectrum) s (t - s) :=
  adamsFirstPageIteratedEquiv H R K SphereSpectrum s t

#print axioms KIP126.StableHomotopy.Cohomology.coefficientTensorEquiv
#print axioms KIP126.Classical.Adams.adamsNextHomologyTensorEquiv_boundary
#print axioms KIP126.Classical.Adams.adamsFirstPageIteratedEquiv
