import KIP126.Def.ClassicalAdams.TowerHomology.FirstDifferential.Primitive.Proofs
import KIP126.Def.StableHomotopy.Cohomology.Cooperations.MilnorBasis.Coproduct.Primitive.Proofs

/-! A concrete polynomial coproduct calculation now implies a vanishing
actual tower differential. This does not use the fixed MilnorCooperations
page-comparison axiom, nor assert later survival or nonzero page classes. -/

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

/-- The actual first-page class constructed from the ξ₁^64 cooperation
and a sphere coefficient is a cycle. The polynomial-to-coproduct and
coproduct-to-boundary comparisons are both used as proved theorems. -/
theorem sphereAdamsPageD_one_h6_tensorBoundary
    (hK : Mod2KunnethSuspensionCompatible H R K)
    (hD : Mod2KunnethDiagonalCompatible H R K)
    (hU : Mod2KunnethUnitCompatible H R K)
    (hM : Mod2MilnorCoproductCompatible H R K B)
    (a : Mod2Cooperations H 64) (ha : cooperationMilnorPolynomial H R B 64 a = h6Polynomial)
    (x : Mod2Homology H 0 SphereSpectrum) :
    letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
      fun i => mod2HomologyModule H R i H.HF2
    let y := adamsTensorBoundary H R K SphereSpectrum 64
      (DirectSum.lof (ZMod 2) ℤ _ 64 (a ⊗ₜ[ZMod 2] x))
    (adamsPageD H.unit SphereSpectrum 1 le_rfl (1, 64) (2, 64)).hom
      ((adamsPageOneHomologyEquiv H.unit SphereSpectrum 1 64).symm y) = 0 :=
  sphereAdamsPageD_one_tensorBoundary_primitive H R K hK hD hU 64 64 a
    (cooperationTensorDiagonal_primitive_of_h6Polynomial H R B K hU hM a ha) x

/-- The cooperation used by the actual cycle construction exists uniquely
from the reduced basis. No separate representative or page-differential
existence input is introduced. -/
theorem sphereAdamsPageD_one_h6_tensorBoundary_existsUnique
    (hK : Mod2KunnethSuspensionCompatible H R K)
    (hD : Mod2KunnethDiagonalCompatible H R K)
    (hU : Mod2KunnethUnitCompatible H R K)
    (hM : Mod2MilnorCoproductCompatible H R K B) :
    letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
      fun i => mod2HomologyModule H R i H.HF2
    ∃! a : Mod2Cooperations H 64,
      cooperationMilnorPolynomial H R B 64 a = h6Polynomial ∧
        ∀ x : Mod2Homology H 0 SphereSpectrum,
          (adamsPageD H.unit SphereSpectrum 1 le_rfl (1, 64) (2, 64)).hom
            ((adamsPageOneHomologyEquiv H.unit SphereSpectrum 1 64).symm
              (adamsTensorBoundary H R K SphereSpectrum 64
                (DirectSum.lof (ZMod 2) ℤ _ 64 (a ⊗ₜ[ZMod 2] x)))) = 0 := by
  obtain ⟨a, ha, hu⟩ := cooperationMilnorPolynomial_h6_existsUnique H R B
  exact ⟨a, ⟨ha, fun x => sphereAdamsPageD_one_h6_tensorBoundary H R K B hK hD hU hM a ha x⟩,
    fun b hb => hu b hb.1⟩

end

end KIP126.Classical.Adams
