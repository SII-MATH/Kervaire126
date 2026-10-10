import KIP126.Def.ClassicalAdams.TowerHomology.MilnorCoordinates.H6.Proofs
import KIP126.Def.ClassicalAdams.TowerHomology.MilnorCoordinates.SphereTensor.Proofs
import KIP126.Def.ClassicalAdams.TowerHomology.MilnorCoordinates.SphereTensor.Reduced.Square.Proofs
import KIP126.Def.ClassicalAdams.TowerHomology.MilnorCoordinates.Boundary.First.Polynomial.Proofs
import Lean.Elab.Command

/-! All-filtration coordinates and their representative-level d₁ formula
come from the actual tower, with explicit below-page inputs. -/

open Lean Elab Command in
run_cmd do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in [``KIP126.Classical.Adams.sphereHomologyCoefficientF2Equiv,
      ``KIP126.Classical.Adams.sphereHomologyEmptyWordEquiv,
      ``KIP126.Classical.Adams.sphereHomologyScalarEquiv,
      ``KIP126.Classical.Adams.sphereCooperationTensorEquiv,
      ``KIP126.Classical.Adams.sphereHomologyScalarEquiv_symm_one,
      ``KIP126.Classical.Adams.sphereHomologyScalarEquiv_cast_symm_one,
      ``KIP126.Classical.Adams.sphereReducedCooperationTensorEquiv,
      ``KIP126.Classical.Adams.sphereReducedCooperationTensorEquiv_symm_apply,
      ``KIP126.Classical.Adams.sphereReducedCooperationTensorEquiv_inclusion,
      ``KIP126.Classical.Adams.sphereReducedBoundaryEquiv,
      ``KIP126.Classical.Adams.sphereReducedBoundaryEquiv_apply,
      ``KIP126.Core.Algebra.gradedTensorLowerEquiv,
      ``KIP126.Core.Algebra.gradedTensorLowerEquiv_toLinearMap,
      ``KIP126.Core.Algebra.gradedTensorLowerMap_injective,
      ``KIP126.Classical.Adams.sphereCooperationSquareBoundary,
      ``KIP126.Classical.Adams.sphereDoubleReducedBoundaryEquiv,
      ``KIP126.Classical.Adams.sphereSecondReducedBoundaryEquiv,
      ``KIP126.Classical.Adams.sphereCooperationSquareBoundary_lof_tmul,
      ``KIP126.Classical.Adams.sphereDoubleReducedBoundaryEquiv_lof_tmul,
      ``KIP126.Classical.Adams.sphereDoubleReducedBoundary_injective,
      ``KIP126.Classical.Adams.sphereDoubleReducedBoundaryEquiv_inclusion,
      ``KIP126.Classical.Adams.sphereCooperationTensorEquiv_symm_apply,
      ``KIP126.Classical.Adams.sphereCooperationTensor_existsUnique,
      ``KIP126.Steenrod.Milnor.singleMilnorWordEquiv,
      ``KIP126.Steenrod.Milnor.singleMilnorWord_exponents,
      ``KIP126.Steenrod.Milnor.wordConsEquiv_zero,
      ``KIP126.Steenrod.Milnor.milnorWordPolynomial,
      ``KIP126.Steenrod.Milnor.milnorWordPolynomial_single,
      ``KIP126.Steenrod.Milnor.milnorWordPolynomial_injective,
      ``KIP126.Steenrod.Milnor.milnorWordPolynomial_eq_cochainsWordEquiv_symm,
      ``KIP126.Classical.Adams.sphereTowerHomologyWordEquiv_boundary_reduced,
      ``KIP126.Classical.Adams.sphereTowerHomologyWordEquiv_boundary_basis_single,
      ``KIP126.Classical.Adams.sphereFirstPageMilnorEquiv_boundary_reduced,
      ``KIP126.Classical.Adams.sphereTowerHomologyWordEquiv_firstBoundary_basis,
      ``KIP126.Classical.Adams.sphereTowerHomologyWordEquiv_firstBoundary_reduced,
      ``KIP126.Classical.Adams.sphereFirstBoundary_polynomial_reduced,
      ``KIP126.Classical.Adams.sphereTowerHomologyWordEquiv,
      ``KIP126.Classical.Adams.sphereFirstPageMilnorEquiv,
      ``KIP126.Classical.Adams.sphereTowerHomologyWordEquiv_succ,
      ``KIP126.Classical.Adams.sphereTowerHomologyWordEquiv_d1,
      ``KIP126.Classical.Adams.sphereMilnorUnitCoefficient,
      ``KIP126.Classical.Adams.sphereMilnorUnitCoefficient_ne_zero,
      ``KIP126.Classical.Adams.cooperation_h6_eq_reduced_basis,
      ``KIP126.Classical.Adams.sphereTowerHomologyWordEquiv_unitCoefficient,
      ``KIP126.Classical.Adams.sphereTowerHomologyWordEquiv_h6,
      ``KIP126.Classical.Adams.sphereTowerHomologyWordEquiv_h6_double,
      ``KIP126.Classical.Adams.sphereFirstPageMilnorEquiv_h6,
      ``KIP126.Classical.Adams.sphereFirstPageMilnorEquiv_h6_double] do
    for a in ← liftCoreM (collectAxioms declaration) do
      unless allowed.contains a do
        throwError "unexpected derived Milnor-coordinate dependency: {declaration}: {a}"
  for m in (← getEnv).allImportedModuleNames do
    if (`KIP126.Mathlib).isPrefixOf m || (`KIPBase).isPrefixOf m ||
        (`Mathlib.Algebra.Homology.SpectralSequence).isPrefixOf m ||
        (`KIP126.Def.ClassicalAdams.MilnorCooperations).isPrefixOf m ||
        (`KIP126.Def.StageInput).isPrefixOf m ||
        (`KIP126.Def.AdamsE2).isPrefixOf m then
      throwError "unexpected derived Milnor-coordinate import: {m}"

open CategoryTheory MonoidalCategory KIP126.Classical.Adams KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology in
noncomputable example {C : Type*} [StableHomotopyCategory C] [MonoidalPreadditive C]
    [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C))
    (R : Mod2RingStructure H) (K : Mod2CooperationKunneth H R)
    (B : Mod2ReducedMilnorBasis H R)
    [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]
    (s t : ℕ) :
    letI := adamsPageF2Module H R SphereSpectrum 1 le_rfl s t
    adamsPage H.unit SphereSpectrum 1 le_rfl s t ≃ₗ[ZMod 2]
      KIP126.Steenrod.Milnor.cochains s t :=
  sphereFirstPageMilnorEquiv H R K B s t

#print axioms KIP126.Classical.Adams.sphereFirstPageMilnorEquiv
#print axioms KIP126.Classical.Adams.sphereTowerHomologyWordEquiv_d1
#print axioms KIP126.Classical.Adams.sphereFirstPageMilnorEquiv_h6_double
#print axioms KIP126.Classical.Adams.sphereCooperationTensor_existsUnique
#print axioms KIP126.Classical.Adams.sphereFirstBoundary_polynomial_reduced
#print axioms KIP126.Classical.Adams.sphereDoubleReducedBoundaryEquiv_inclusion
