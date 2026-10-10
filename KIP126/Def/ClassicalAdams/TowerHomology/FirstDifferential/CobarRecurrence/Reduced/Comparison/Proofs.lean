import KIP126.Def.ClassicalAdams.TowerHomology.FirstDifferential.CobarRecurrence.Reduced.Proofs
import KIP126.Def.ClassicalAdams.TowerHomology.MilnorCoordinates.SphereTensor.Reduced.Square.Proofs

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology KIP126.Steenrod.Milnor KIP126.Core.Algebra

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C))
  (R : Mod2RingStructure H) (K : Mod2CooperationKunneth H R)
  (B : Mod2ReducedMilnorBasis H R)
  [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]
  [(mod2UnitNatTrans H).CommShift ℤ]
  (hK : Mod2KunnethSuspensionCompatible H R K)
  (hD : Mod2KunnethDiagonalCompatible H R K)
  (hU : Mod2KunnethUnitCompatible H R K)
  (hM : Mod2MilnorCoproductCompatible H R K B)

include hK hD hU hM

/-- Conjugating the actual first incoming differential by the derived
boundary equivalences gives the actual reduced coproduct, in every degree. -/
theorem sphereAdamsHomologyD1_reduced_comparison (n : ℤ) :
    letI : ∀ i, Module F2 (Mod2Cooperations H i) :=
      fun i => mod2HomologyModule H R i H.HF2
    letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) :=
      fun i => mod2HF2HomotopyModule H R i
    ∀ a : LinearMap.ker (cooperationCounitF2 H R n),
      adamsHomologyD1 H (adamsTower H.unit SphereSpectrum 1) (n - 1)
        (sphereReducedBoundaryEquiv H R K n a) =
      sphereSecondReducedBoundaryEquiv H R K n
        (cooperationReducedCobarDiagonal H R B K hU hM n a) := by
  letI : ∀ i, Module F2 (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) :=
    fun i => mod2HF2HomotopyModule H R i
  intro a
  apply (adamsNextHomologyTensorEquiv H R K (adamsTower H.unit SphereSpectrum 1) (n - 1)).injective
  change _ = (adamsNextHomologyTensorEquiv H R K _ _)
    ((adamsNextHomologyTensorEquiv H R K _ _).symm
      (sphereDoubleReducedBoundaryEquiv H R K n
        (cooperationReducedCobarDiagonal H R B K hU hM n a)))
  rw [LinearEquiv.apply_symm_apply]
  apply reducedCooperationTensorInclusion_injective H R _ _
  rw [sphereReducedBoundaryEquiv_apply, sphereDoubleReducedBoundaryEquiv_inclusion]
  exact sphereAdamsHomologyD1_firstBoundary_reduced H R K B hK hD hU hM n a

/-- The faithful two-slot polynomial of the actual first incoming
differential is the existing cobar differential, not a comparison axiom. -/
theorem sphereAdamsHomologyD1_reduced_polynomial (n : ℤ) :
    letI : ∀ i, Module F2 (Mod2Cooperations H i) :=
      fun i => mod2HomologyModule H R i H.HF2
    letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) :=
      fun i => mod2HF2HomotopyModule H R i
    ∀ a : LinearMap.ker (cooperationCounitF2 H R n),
      cooperationTensorMilnorPolynomial H R B n
        (reducedCooperationSquareInclusion H R n
          ((sphereSecondReducedBoundaryEquiv H R K n).symm
            (adamsHomologyD1 H (adamsTower H.unit SphereSpectrum 1) (n - 1)
              (sphereReducedBoundaryEquiv H R K n a)))) =
        differentialPolynomial 1 (cooperationMilnorPolynomial H R B n a.val) := by
  letI : ∀ i, Module F2 (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) :=
    fun i => mod2HF2HomotopyModule H R i
  intro a
  rw [sphereAdamsHomologyD1_reduced_comparison H R K B hK hD hU hM,
    LinearEquiv.symm_apply_apply]
  exact cooperationReducedCobarDiagonal_polynomial H R B K hU hM n a

/-- An actual incoming boundary is equivalent to a polynomial cobar equation.
The reverse implication uses faithful tensor coordinates; it is not only a
necessary condition. This treats the first incoming differential, not higher pages. -/
theorem sphereAdamsHomologyD1_mem_range_iff_polynomial (n : ℤ)
    (y : mod2HomologyF2 H R (n - 1 - 1) (adamsTower H.unit SphereSpectrum 2)) :
    letI : ∀ i, Module F2 (Mod2Cooperations H i) :=
      fun i => mod2HomologyModule H R i H.HF2
    letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) :=
      fun i => mod2HF2HomotopyModule H R i
    (∃ x : mod2HomologyF2 H R (n - 1) (adamsTower H.unit SphereSpectrum 1),
      adamsHomologyD1 H (adamsTower H.unit SphereSpectrum 1) (n - 1) x = y) ↔
    ∃ a : LinearMap.ker (cooperationCounitF2 H R n),
      differentialPolynomial 1 (cooperationMilnorPolynomial H R B n a.val) =
        cooperationTensorMilnorPolynomial H R B n
          (reducedCooperationSquareInclusion H R n ((sphereSecondReducedBoundaryEquiv H R K n).symm y)) := by
  letI : ∀ i, Module F2 (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) :=
    fun i => mod2HF2HomotopyModule H R i
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨a, rfl⟩ := (sphereReducedBoundaryEquiv H R K n).surjective x
    refine ⟨a, ?_⟩
    have h := sphereAdamsHomologyD1_reduced_polynomial H R K B hK hD hU hM n a
    rw [hx] at h
    exact h.symm
  · rintro ⟨a, ha⟩
    have he : cooperationReducedCobarDiagonal H R B K hU hM n a =
        (sphereSecondReducedBoundaryEquiv H R K n).symm y := by
      apply reducedCooperationSquareInclusion_injective H R n
      apply cooperationTensorMilnorPolynomial_injective H R B n
      exact (cooperationReducedCobarDiagonal_polynomial H R B K hU hM n a).trans ha
    refine ⟨sphereReducedBoundaryEquiv H R K n a, ?_⟩
    rw [sphereAdamsHomologyD1_reduced_comparison H R K B hK hD hU hM, he,
      LinearEquiv.apply_symm_apply]

end
end KIP126.Classical.Adams
