import KIP126.Def.ClassicalAdams.TowerHomology.FirstDifferential.Primitive.H6.Nonvanishing.Proofs
import KIP126.Def.ClassicalAdams.TowerHomology.FirstDifferential.Sphere.PageTwo.Proofs

/-! The primitive h-six polynomial gives a nonzero actual second-page
class. Its first-page provenance is part of the statement. -/

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

/-- A nonzero E₂ representative whose E₁ class is constructed from ξ₁^64.
This does not assert equality with the fixed standard h₆ or permanence. -/
theorem sphereAdamsPageTwo_h6_nonzero_exists
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
          (adamsCycleBoundaries H.unit SphereSpectrum 2 (by decide) 1 64).mkQ u ≠ 0 := by
  obtain ⟨a, ha, x, hx, hz, hd⟩ :=
    sphereAdamsPageOne_h6_nonzero_cycle_exists H R K B hK hD hU hM
  obtain ⟨u, hu, hne⟩ := sphereAdamsPageTwo_nonzero_of_first_cycle H 64 _ hz hd
  exact ⟨a, ha, x, hx, u, hu, hne⟩

end

end KIP126.Classical.Adams
