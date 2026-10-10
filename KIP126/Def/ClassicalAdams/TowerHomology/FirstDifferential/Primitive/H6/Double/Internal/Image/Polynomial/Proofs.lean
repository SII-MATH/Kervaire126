import KIP126.Def.ClassicalAdams.TowerHomology.MilnorCoordinates.SphereTensor.Reduced.Square.H6.Proofs
import KIP126.Def.ClassicalAdams.TowerHomology.FirstDifferential.CobarRecurrence.Reduced.Comparison.Proofs
import KIP126.Def.StableHomotopy.Cohomology.Cooperations.MilnorBasis.Cochains.Proofs

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
  (a : Mod2Cooperations H 64) (ha : cooperationMilnorPolynomial H R B 64 a = h6Polynomial)

/-- Move the existing internal zero test through the actual first-page
homology equivalences. No polynomial input is needed for this transport. -/
theorem sphereH6DoubleInternalE2_eq_zero_iff_homologyD1
    (x : Mod2Homology H 0 SphereSpectrum) :
    sphereH6DoubleInternalE2 H R K B hK hD hU hM a ha x = 0 ↔
      ∃ z : Mod2Homology H 127 (adamsTower H.unit SphereSpectrum 1),
        adamsHomologyD1 H (adamsTower H.unit SphereSpectrum 1) 127 z =
          sphereH6DoubleTensorRepresentative H R K a x := by
  refine (sphereH6DoubleInternalE2_eq_zero_iff_is_differential H R K B hK hD hU hM a ha x).trans ?_
  have hp (z : adamsPage H.unit SphereSpectrum 1 le_rfl 1 128) :
      adamsPageOneHomologyEquiv H.unit SphereSpectrum 2 128
        ((adamsPageD H.unit SphereSpectrum 1 le_rfl (1, 128) (2, 128)).hom z) =
      adamsHomologyD1 H (adamsTower H.unit SphereSpectrum 1) 127
        (adamsPageOneHomologyEquiv H.unit SphereSpectrum 1 128 z) :=
    adamsPageD_one_homologyD1 H SphereSpectrum 1 128 z
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨adamsPageOneHomologyEquiv H.unit SphereSpectrum 1 128 z, ?_⟩
    have h := (hp z).symm.trans
      (congrArg (adamsPageOneHomologyEquiv H.unit SphereSpectrum 2 128) hz)
    exact h.trans (LinearEquiv.apply_symm_apply _ _)
  · rintro ⟨z, hz⟩
    refine ⟨(adamsPageOneHomologyEquiv H.unit SphereSpectrum 1 128).symm z, ?_⟩
    apply (adamsPageOneHomologyEquiv H.unit SphereSpectrum 2 128).injective
    rw [hp, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    exact hz

/-- For the normalized sphere coefficient, the internal square class
vanishes exactly when its specified polynomial is an incoming cobar image. -/
theorem sphereH6DoubleInternalE2_eq_zero_iff_polynomial :
    letI : ∀ i, Module F2 (Mod2Cooperations H i) :=
      fun i => mod2HomologyModule H R i H.HF2
    letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) :=
      fun i => mod2HF2HomotopyModule H R i
    sphereH6DoubleInternalE2 H R K B hK hD hU hM a ha (sphereMilnorUnitCoefficient H R) = 0 ↔
      ∃ b : LinearMap.ker (cooperationCounitF2 H R 128),
        differentialPolynomial 1 (cooperationMilnorPolynomial H R B 128 b.val) =
          h6SquareCochain.val := by
  letI : ∀ i, Module F2 (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) :=
    fun i => mod2HF2HomotopyModule H R i
  refine (sphereH6DoubleInternalE2_eq_zero_iff_homologyD1 H R K B hK hD hU hM a ha
    (sphereMilnorUnitCoefficient H R)).trans ?_
  have h := sphereAdamsHomologyD1_mem_range_iff_polynomial H R K B hK hD hU hM 128
    (sphereH6DoubleTensorRepresentative H R K a (sphereMilnorUnitCoefficient H R))
  rw [sphereSecondReducedBoundaryEquiv_h6_double_polynomial H R K B a ha] at h
  exact h

/-- The remaining vanishing question is entirely in the existing
normalized Milnor cobar complex. The source ranges over all cochains. -/
theorem sphereH6DoubleInternalE2_eq_zero_iff_cobar_boundary :
    sphereH6DoubleInternalE2 H R K B hK hD hU hM a ha (sphereMilnorUnitCoefficient H R) = 0 ↔
      ∃ b : cochains 1 128, differential 1 128 b = h6SquareCochain :=
  (sphereH6DoubleInternalE2_eq_zero_iff_polynomial H R K B hK hD hU hM a ha).trans
    (reducedCooperation_polynomial_boundary_iff H R B 128 h6SquareCochain)

/-- A purely algebraic non-boundary calculation is both necessary and
sufficient for nonvanishing of this actual internal E₂ representative.
It does not assert the calculation or identify the fixed Lin class. -/
theorem sphereH6DoubleInternalE2_ne_zero_iff_cobar_nonboundary :
    sphereH6DoubleInternalE2 H R K B hK hD hU hM a ha (sphereMilnorUnitCoefficient H R) ≠ 0 ↔
      ∀ b : cochains 1 128, differential 1 128 b ≠ h6SquareCochain := by
  simpa only [not_exists] using
    not_congr (sphereH6DoubleInternalE2_eq_zero_iff_cobar_boundary H R K B hK hD hU hM a ha)

end
end KIP126.Classical.Adams
