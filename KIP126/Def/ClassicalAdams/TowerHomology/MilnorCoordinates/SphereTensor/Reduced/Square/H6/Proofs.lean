import KIP126.Def.ClassicalAdams.TowerHomology.MilnorCoordinates.SphereTensor.Reduced.Square.Proofs
import KIP126.Def.ClassicalAdams.TowerHomology.FirstDifferential.Primitive.H6.Double.Internal.Image.Proofs
import KIP126.Def.Steenrod.MilnorCobar.Data

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology KIP126.Steenrod.Milnor KIP126.Core.Algebra
open scoped TensorProduct DirectSum

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C))
  (R : Mod2RingStructure H) (K : Mod2CooperationKunneth H R)
  [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]

/-- The derived two-boundary equivalence sends the reduced tensor square
to the original twice-applied boundary representative with unit coefficient. -/
theorem sphereSecondReducedBoundaryEquiv_h6_double :
    letI : ∀ i, Module F2 (Mod2Cooperations H i) :=
      fun i => mod2HomologyModule H R i H.HF2
    letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) :=
      fun i => mod2HF2HomotopyModule H R i
    ∀ a : LinearMap.ker (cooperationCounitF2 H R 64),
      sphereSecondReducedBoundaryEquiv H R K 128
        (DirectSum.lof F2 ℤ _ 64 (a ⊗ₜ[F2] a)) =
      sphereH6DoubleTensorRepresentative H R K a.val (sphereMilnorUnitCoefficient H R) := by
  letI : ∀ i, Module F2 (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) :=
    fun i => mod2HF2HomotopyModule H R i
  intro a
  apply (adamsNextHomologyTensorEquiv H R K (adamsTower H.unit SphereSpectrum 1) 127).injective
  change (adamsNextHomologyTensorEquiv H R K _ _)
    ((adamsNextHomologyTensorEquiv H R K _ _).symm
      (sphereDoubleReducedBoundaryEquiv H R K 128 _)) = _
  rw [LinearEquiv.apply_symm_apply]
  apply reducedCooperationTensorInclusion_injective H R _ _
  rw [sphereDoubleReducedBoundaryEquiv_lof_tmul, reducedCooperationTensorInclusion_lof_tmul]
  have h := sphereH6DoubleTensorRepresentative_normalized H R K a.val (sphereMilnorUnitCoefficient H R)
  refine Eq.trans ?_ h.symm
  rw [sphereCooperationTensorEquiv_symm_apply]
  rfl

/-- The polynomial target in the incoming-image test is exactly the
existing standard square cochain, with no new comparison assumption. -/
theorem sphereSecondReducedBoundaryEquiv_h6_double_polynomial
    (B : Mod2ReducedMilnorBasis H R) (a : Mod2Cooperations H 64)
    (ha : cooperationMilnorPolynomial H R B 64 a = h6Polynomial) :
    cooperationTensorMilnorPolynomial H R B 128
      (reducedCooperationSquareInclusion H R 128
        ((sphereSecondReducedBoundaryEquiv H R K 128).symm
          (sphereH6DoubleTensorRepresentative H R K a (sphereMilnorUnitCoefficient H R)))) =
      h6SquareCochain.val := by
  letI : ∀ i, Module F2 (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) :=
    fun i => mod2HF2HomotopyModule H R i
  have har : a ∈ LinearMap.ker (cooperationCounitF2 H R 64) := by
    rw [LinearMap.mem_ker, cooperationCounitF2_eq_zero_of_ne H R 64 (by decide), LinearMap.zero_apply]
  let ar : LinearMap.ker (cooperationCounitF2 H R 64) := ⟨a, har⟩
  have h := sphereSecondReducedBoundaryEquiv_h6_double H R K ar
  rw [← h, LinearEquiv.symm_apply_apply, reducedCooperationSquareInclusion_lof_tmul]
  have hp := cooperationTensorMilnorPolynomial_lof_tmul H R B 128 64 a a
  exact hp.trans (by
    change cupPolynomial (cooperationMilnorPolynomial H R B 64 a)
      (cooperationMilnorPolynomial H R B 64 a) = cupPolynomial h6Polynomial h6Polynomial
    rw [ha])

end
end KIP126.Classical.Adams
