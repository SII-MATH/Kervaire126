import KIP126.Def.ClassicalAdams.TowerHomology.FirstDifferential.Primitive.H6.PageTwo.Proofs
import KIP126.Def.ClassicalAdams.TowerSSData.FirstCycles.Proofs

/-! The polynomial construction reaches the existing internal SSData page,
with the actual tower representative retained. No fixed comparison input
or Mathlib spectral-sequence adapter enters this construction. -/

namespace KIP126.Classical.Adams

noncomputable section

open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology KIP126.Steenrod.Milnor
open scoped TensorProduct DirectSum

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C))
  (R : Mod2RingStructure H) (K : Mod2CooperationKunneth H R)
  (B : Mod2ReducedMilnorBasis H R)
  [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]
  [(mod2UnitNatTrans H).CommShift ℤ]

/-- A nonzero internal E₂ class with the specified actual polynomial
representative, under explicit low-level coherence hypotheses. -/
theorem sphereAdamsInternalE2_h6_nonzero_exists
    (hK : Mod2KunnethSuspensionCompatible H R K)
    (hD : Mod2KunnethDiagonalCompatible H R K)
    (hU : Mod2KunnethUnitCompatible H R K)
    (hM : Mod2MilnorCoproductCompatible H R K B) :
    letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
      fun i => mod2HomologyModule H R i H.HF2
    ∃ a : Mod2Cooperations H 64,
      cooperationMilnorPolynomial H R B 64 a = h6Polynomial ∧
      ∃ x : Mod2Homology H 0 SphereSpectrum, x ≠ 0 ∧
        ∃ u : adamsCycles H.unit SphereSpectrum 2 (by decide) 1 64,
          adamsNextCycleToPage H.unit SphereSpectrum 1 le_rfl 1 64 u =
            (adamsPageOneHomologyEquiv H.unit SphereSpectrum 1 64).symm
              (adamsTensorBoundary H R K SphereSpectrum 64
                (DirectSum.lof (ZMod 2) ℤ _ 64 (a ⊗ₜ[ZMod 2] x))) ∧
          ∃ z : (adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page 2 (1, 64),
            z ≠ 0 ∧ (adamsTowerSSDataPageIso H.unit SphereSpectrum 1 64 0).hom z =
              (adamsCycleBoundaries H.unit SphereSpectrum 2 (by decide) 1 64).mkQ u := by
  obtain ⟨a, ha, x, hx, u, hu, hne⟩ :=
    sphereAdamsPageTwo_h6_nonzero_exists H R K B hK hD hU hM
  let y := adamsNextCycleToPage H.unit SphereSpectrum 1 le_rfl 1 64 u
  have hy : adamsDifferential H.unit SphereSpectrum 1 le_rfl 1 64 y = 0 :=
    adamsNextCycle_differential_zero H.unit SphereSpectrum 1 le_rfl 1 64 u
  refine ⟨a, ha, x, hx, u, hu,
    adamsTowerE2OfFirstCycle H.unit SphereSpectrum 1 64 y hy, ?_,
    adamsTowerE2OfFirstCycle_comparison H.unit SphereSpectrum 1 64 y hy u rfl⟩
  intro hz
  have hb := (adamsTowerE2OfFirstCycle_eq_zero_iff H.unit SphereSpectrum 1 64 y hy u rfl).mp hz
  exact hne ((adamsPage_mk_eq_zero H.unit SphereSpectrum 2 (by decide) 1 64 u).mpr hb)

end
end KIP126.Classical.Adams
