import KIP126.Def.ClassicalAdams.TowerHomology.FirstDifferential.Primitive.H6.Proofs
import KIP126.Def.ClassicalAdams.TowerHomology.Coaction.Tensor.Nonvanishing.Proofs
import KIP126.Def.StableHomotopy.Cohomology.Sphere.Nonvanishing.Proofs

/-! A nonzero cycle on the actual first sphere Adams page, constructed from
the primitive polynomial and a genuine nonzero sphere coefficient. This
does not identify the fixed standard class or assert higher-page survival. -/

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

/-- For any nonzero sphere coefficient, the actual first-page class
constructed from ξ₁^64 is nonzero. No coproduct compatibility is needed
for nonvanishing itself. -/
theorem sphereAdamsPageOne_h6_tensorBoundary_ne_zero
    (a : Mod2Cooperations H 64) (ha : cooperationMilnorPolynomial H R B 64 a = h6Polynomial)
    (x : Mod2Homology H 0 SphereSpectrum) (hx : x ≠ 0) :
    letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
      fun i => mod2HomologyModule H R i H.HF2
    (adamsPageOneHomologyEquiv H.unit SphereSpectrum 1 64).symm
      (adamsTensorBoundary H R K SphereSpectrum 64
        (DirectSum.lof (ZMod 2) ℤ _ 64 (a ⊗ₜ[ZMod 2] x))) ≠ 0 :=
  sphereAdamsPageOne_tensorBoundary_ne_zero H R K 64 64 (by decide) a
    (cooperation_ne_zero_of_h6Polynomial H R B a ha) x hx

variable [(mod2UnitNatTrans H).CommShift ℤ]

/-- A genuine nonzero first-page cycle is obtained without a separate
representative-existence or nonvanishing input. All structural comparisons
are explicit low-level hypotheses, not the fixed page-comparison axiom. -/
theorem sphereAdamsPageOne_h6_nonzero_cycle_exists
    (hK : Mod2KunnethSuspensionCompatible H R K)
    (hD : Mod2KunnethDiagonalCompatible H R K)
    (hU : Mod2KunnethUnitCompatible H R K)
    (hM : Mod2MilnorCoproductCompatible H R K B) :
    letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
      fun i => mod2HomologyModule H R i H.HF2
    ∃ a : Mod2Cooperations H 64,
      cooperationMilnorPolynomial H R B 64 a = h6Polynomial ∧
      ∃ x : Mod2Homology H 0 SphereSpectrum,
        let z := (adamsPageOneHomologyEquiv H.unit SphereSpectrum 1 64).symm
          (adamsTensorBoundary H R K SphereSpectrum 64
            (DirectSum.lof (ZMod 2) ℤ _ 64 (a ⊗ₜ[ZMod 2] x)))
        x ≠ 0 ∧ z ≠ 0 ∧
          (adamsPageD H.unit SphereSpectrum 1 le_rfl (1, 64) (2, 64)).hom z = 0 := by
  obtain ⟨a, ha, _⟩ := cooperationMilnorPolynomial_h6_existsUnique H R B
  obtain ⟨x, hx⟩ := mod2SphereHomology_exists_ne_zero H
  exact ⟨a, ha, x, hx, sphereAdamsPageOne_h6_tensorBoundary_ne_zero H R K B a ha x hx,
    sphereAdamsPageD_one_h6_tensorBoundary H R K B hK hD hU hM a ha x⟩

end

end KIP126.Classical.Adams
