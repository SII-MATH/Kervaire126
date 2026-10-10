import KIP126.Def.ClassicalAdams.TowerHomology.MilnorCoordinates.H6.Data
import KIP126.Def.ClassicalAdams.TowerHomology.MilnorCoordinates.Proofs
import KIP126.Def.ClassicalAdams.TowerHomology.MilnorCoordinates.Boundary.First.Proofs
import KIP126.Def.ClassicalAdams.TowerHomology.Coaction.Tensor.Coordinates.Proofs
import KIP126.Def.StableHomotopy.Cohomology.Cooperations.MilnorBasis.Elementary.Proofs
import KIP126.Def.ClassicalAdams.TowerHomology.FirstDifferential.Primitive.H6.Double.Data
import KIP126.Def.StableHomotopy.Cohomology.Cooperations.MilnorBasis.Coproduct.Primitive.Proofs
import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Monomials.Words.H6.Proofs

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology KIP126.Steenrod.Milnor
open scoped TensorProduct DirectSum

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)

/-- The normalized coefficient is nonzero by its explicitly specified coordinate. -/
theorem sphereMilnorUnitCoefficient_ne_zero : sphereMilnorUnitCoefficient H R ≠ 0 := by
  intro h
  have hz := congrArg (sphereHomologyEmptyWordEquiv H R 0) h
  change (sphereHomologyEmptyWordEquiv H R 0)
    ((sphereHomologyEmptyWordEquiv H R 0).symm _) = _ at hz
  erw [LinearEquiv.apply_symm_apply, map_zero] at hz
  have := congrArg (fun z => z emptyMilnorWord) hz
  simp at this

variable (K : Mod2CooperationKunneth H R) (B : Mod2ReducedMilnorBasis H R)
  [HasFunctorialCofiber (C := C)]
  [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]

omit [HasFunctorialCofiber (C := C)] [(tensorLeft H.HF2).CommShift ℤ]
  [(tensorLeft H.HF2).IsTriangulated] in
/-- The actual cooperation with polynomial ξ₁^64 is the corresponding
reduced basis vector, not an arbitrary degree-64 element. -/
theorem cooperation_h6_eq_reduced_basis (a : Mod2Cooperations H 64)
    (ha : cooperationMilnorPolynomial H R B 64 a = h6Polynomial) :
    a = ((B.basis 64) h6PositiveMonomial).val := by
  apply cooperationMilnorPolynomial_injective H R B 64
  rw [ha, cooperationMilnorPolynomial_reduced_basis]
  simp [milnorMonomialPolynomial, h6PositiveMonomial, h6Polynomial,
    MvPolynomial.X_pow_eq_monomial]

/-- The chosen sphere coefficient is exactly the empty word at stage zero. -/
theorem sphereTowerHomologyWordEquiv_unitCoefficient :
    sphereTowerHomologyWordEquiv H R K B 0 0 (sphereMilnorUnitCoefficient H R) =
      Finsupp.single emptyMilnorWord 1 := by
  change (sphereHomologyEmptyWordEquiv H R 0)
    ((sphereHomologyEmptyWordEquiv H R 0).symm _) = _
  exact LinearEquiv.apply_symm_apply _ _

/-- Actual first-stage coordinates of the h₆ tensor-boundary representative. -/
theorem sphereTowerHomologyWordEquiv_h6 (a : Mod2Cooperations H 64)
    (ha : cooperationMilnorPolynomial H R B 64 a = h6Polynomial) :
    sphereTowerHomologyWordEquiv H R K B 1 63
      (sphereH6TensorRepresentative H R K a (sphereMilnorUnitCoefficient H R)) =
      Finsupp.single h6MilnorWord 1 := by
  letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  letI : ∀ i, Module (ZMod 2) (HomotopyGroup i H.HF2) :=
    fun i => mod2HF2HomotopyModule H R i
  rw [cooperation_h6_eq_reduced_basis H R B a ha]
  have h := sphereTowerHomologyWordEquiv_firstBoundary_basis H R K B 63 h6PositiveMonomial
  rw [sphereCooperationTensorEquiv_symm_apply] at h
  have hd : singleMilnorWordEquiv 64 h6PositiveMonomial = h6MilnorWord :=
    (wordConsEquiv_zero 64 h6PositiveMonomial emptyMilnorWord).symm
  exact h.trans (congrArg (fun d : MilnorWord 1 64 => Finsupp.single d (1 : ZMod 2)) hd)

/-- The double actual boundary has precisely the two-slot h₆-square word. -/
theorem sphereTowerHomologyWordEquiv_h6_double (a : Mod2Cooperations H 64)
    (ha : cooperationMilnorPolynomial H R B 64 a = h6Polynomial) :
    sphereTowerHomologyWordEquiv H R K B 2 126
      (sphereH6DoubleTensorRepresentative H R K a (sphereMilnorUnitCoefficient H R)) =
      Finsupp.single h6SquareMilnorWord 1 := by
  letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  letI : ∀ i, Module (ZMod 2) (HomotopyGroup i H.HF2) :=
    fun i => mod2HF2HomotopyModule H R i
  change reducedTensorMilnorWordEquiv H R B
    (fun i => mod2HomologyF2 H R i (adamsTower H.unit SphereSpectrum 1))
    1 (sphereTowerHomologyWordEquiv H R K B 1) 126
      (adamsNextHomologyTensorEquiv H R K (adamsTower H.unit SphereSpectrum 1) 127
        (adamsTensorBoundary H R K (adamsTower H.unit SphereSpectrum 1) 127
          (DirectSum.lof (ZMod 2) ℤ _ 64
            (a ⊗ₜ[ZMod 2] sphereH6TensorRepresentative H R K a (sphereMilnorUnitCoefficient H R))))) = _
  have hab := cooperation_h6_eq_reduced_basis H R B a ha
  nth_rw 1 [hab]
  rw [adamsNextHomologyTensorEquiv_boundary_lof_tmul]
  exact reducedTensorMilnorWordEquiv_basis_single H R B
    (fun i => mod2HomologyF2 H R i (adamsTower H.unit SphereSpectrum 1))
    1 (sphereTowerHomologyWordEquiv H R K B 1) 126 64
    h6PositiveMonomial (sphereH6TensorRepresentative H R K a (sphereMilnorUnitCoefficient H R))
    h6MilnorWord 1 (sphereTowerHomologyWordEquiv_h6 H R K B a ha)

/-- The derived actual first-page coordinates send the constructed class
to the existing standard one-slot cocycle. -/
theorem sphereFirstPageMilnorEquiv_h6 (a : Mod2Cooperations H 64)
    (ha : cooperationMilnorPolynomial H R B 64 a = h6Polynomial) :
    sphereFirstPageMilnorEquiv H R K B 1 64
      ((adamsPageOneHomologyEquiv H.unit SphereSpectrum 1 64).symm
        (sphereH6TensorRepresentative H R K a (sphereMilnorUnitCoefficient H R))) =
      h6Cochain := by
  apply (cochainsWordEquiv 1 64).injective
  change (cochainsWordEquiv 1 64)
    ((cochainsWordEquiv 1 64).symm
      (sphereTowerHomologyWordEquiv H R K B 1 63
        ((adamsPageOneHomologyEquiv H.unit SphereSpectrum 1 64)
          ((adamsPageOneHomologyEquiv H.unit SphereSpectrum 1 64).symm
            (sphereH6TensorRepresentative H R K a (sphereMilnorUnitCoefficient H R)))))) = _
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
    sphereTowerHomologyWordEquiv_h6 H R K B a ha, cochainsWordEquiv_h6]

/-- The actual double tensor boundary is exactly the specified square
cocycle under the derived first-page coordinates. This is not yet a
comparison with the independently assumed fixed Milnor coordinates. -/
theorem sphereFirstPageMilnorEquiv_h6_double (a : Mod2Cooperations H 64)
    (ha : cooperationMilnorPolynomial H R B 64 a = h6Polynomial) :
    sphereFirstPageMilnorEquiv H R K B 2 128
      ((adamsPageOneHomologyEquiv H.unit SphereSpectrum 2 128).symm
        (sphereH6DoubleTensorRepresentative H R K a (sphereMilnorUnitCoefficient H R))) =
      h6SquareCochain := by
  apply (cochainsWordEquiv 2 128).injective
  change (cochainsWordEquiv 2 128)
    ((cochainsWordEquiv 2 128).symm
      (sphereTowerHomologyWordEquiv H R K B 2 126
        ((adamsPageOneHomologyEquiv H.unit SphereSpectrum 2 128)
          ((adamsPageOneHomologyEquiv H.unit SphereSpectrum 2 128).symm
            (sphereH6DoubleTensorRepresentative H R K a (sphereMilnorUnitCoefficient H R)))))) = _
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
    sphereTowerHomologyWordEquiv_h6_double H R K B a ha, cochainsWordEquiv_h6Square]

end
end KIP126.Classical.Adams
