import KIP126.Main.Solution.Computation.LinProgram.Interpretation.Tower.Proofs

/-! Tower lifting criteria for nonzero survival. -/

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology KIP126.Steenrod.Milnor KIP126.Core.SpectralSequence

local notation "H₀" => standardFoundation.hf2

variable [MonoidalPreadditive standardFoundation.Spectrum]
  (R : Mod2RingStructure H₀) (K : Mod2CooperationKunneth H₀ R)
  (B : Mod2ReducedMilnorBasis H₀ R)
  [(tensorLeft (H₀).HF2).CommShift ℤ] [(tensorLeft (H₀).HF2).IsTriangulated]
  [(mod2UnitNatTrans H₀).CommShift ℤ]
  (hK : Mod2KunnethSuspensionCompatible H₀ R K)
  (hD : Mod2KunnethDiagonalCompatible H₀ R K)
  (hU : Mod2KunnethUnitCompatible H₀ R K)
  (hM : Mod2MilnorCoproductCompatible H₀ R K B)
  (a : Mod2Cooperations H₀ 64) (ha : cooperationMilnorPolynomial H₀ R B 64 a = h6Polynomial)

include hK hD hU hM ha

/-- For any actual Z₂ lift of the double tensor-boundary representative,
the remaining computational target is exactly liftability of that same
representative through every finite stage. This does not prove those lifts. -/
theorem computedH6Square_nonzeroSurvival_iff_double_lifts
    (u : adamsCycleAmbient (H₀).unit SphereSpectrum 2 128)
    (hu : adamsNextCycleToPage (H₀).unit SphereSpectrum 1 le_rfl 2 128 u =
      (adamsPageOneHomologyEquiv (H₀).unit SphereSpectrum 2 128).symm
        (sphereH6DoubleTensorRepresentative H₀ R K a (sphereMilnorUnitCoefficient H₀ R))) :
    NonzeroSurvival sphereAdamsData (2, 128) computedH6Square ↔
      ∀ n : ℕ, u.val ∈ adamsCycles (H₀).unit SphereSpectrum (n + 2) (by omega) 2 128 := by
  have hclass := sphereH6DoubleInternalE2_eq_computedH6Square R K B hK hD hU hM a ha
  have hrep := computedH6Square_of_double_representative R K B hK hD hU hM a ha u hu
  have hne : computedH6Square ≠ 0 := by
    intro h
    exact sphereH6DoubleInternalE2_ne_zero H₀ R K B hK hD hU hM a ha (hclass.trans h)
  exact (sphereAdams_h6_nonzeroSurvival_iff_representative H₀ computedH6Square u hrep).trans
    (and_iff_right hne)

/-- The remaining lifts can be stated entirely using actual homotopy groups
and tower maps: the fixed connecting image in π₁₂₅(T₃S) must come from
π₁₂₅(Tₙ₊₄S) for every n. No compatible family of chosen lifts is assumed. -/
theorem computedH6Square_nonzeroSurvival_iff_double_connecting_lifts
    (u : adamsCycleAmbient (H₀).unit SphereSpectrum 2 128)
    (hu : adamsNextCycleToPage (H₀).unit SphereSpectrum 1 le_rfl 2 128 u =
      (adamsPageOneHomologyEquiv (H₀).unit SphereSpectrum 2 128).symm
        (sphereH6DoubleTensorRepresentative H₀ R K a (sphereMilnorUnitCoefficient H₀ R))) :
    NonzeroSurvival sphereAdamsData (2, 128) computedH6Square ↔
      ∀ n : ℕ, ∃ y : HomotopyGroup 125 (adamsTowerAt (H₀).unit SphereSpectrum ((n : ℤ) + 4)),
        adamsI (H₀).unit SphereSpectrum 125 3 ((n : ℤ) + 4) (by omega) y =
          adamsK (H₀).unit SphereSpectrum 2 128 u.val := by
  refine (computedH6Square_nonzeroSurvival_iff_double_lifts R K B hK hD hU hM a ha u hu).trans ?_
  apply forall_congr'
  intro n
  change (∃ y : HomotopyGroup 125
      (adamsTowerAt (H₀).unit SphereSpectrum (2 + ((n + 2 : ℕ) : ℤ))),
      adamsI (H₀).unit SphereSpectrum 125 3 (2 + ((n + 2 : ℕ) : ℤ)) (by omega) y =
        adamsK (H₀).unit SphereSpectrum 2 128 u.val) ↔ _
  have hindex : (2 : ℤ) + ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 4 := by omega
  have hj : (⟨2 + ((n + 2 : ℕ) : ℤ), by omega⟩ : {j : ℤ // 3 ≤ j}) =
      ⟨(n : ℤ) + 4, by omega⟩ := Subtype.ext hindex
  exact Iff.of_eq (congrArg (fun j : {j : ℤ // 3 ≤ j} =>
    ∃ y : HomotopyGroup 125 (adamsTowerAt (H₀).unit SphereSpectrum j.val),
      adamsI (H₀).unit SphereSpectrum 125 3 j.val j.property y =
        adamsK (H₀).unit SphereSpectrum 2 128 u.val) hj)

end
end KIP126.Classical.Adams
