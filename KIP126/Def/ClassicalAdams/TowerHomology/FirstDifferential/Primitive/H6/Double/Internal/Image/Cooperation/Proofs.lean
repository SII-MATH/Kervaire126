import KIP126.Def.ClassicalAdams.TowerHomology.FirstDifferential.Primitive.H6.Double.Internal.Image.Proofs
import KIP126.Def.ClassicalAdams.TowerHomology.MilnorCoordinates.SphereTensor.Proofs

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology KIP126.Steenrod.Milnor KIP126.Core.Algebra
open scoped TensorProduct DirectSum

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C))
  (R : Mod2RingStructure H) (K : Mod2CooperationKunneth H R)
  (B : Mod2ReducedMilnorBasis H R)
  [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]
  [(mod2UnitNatTrans H).CommShift ℤ]

/-- The possible incoming sources are single degree-128 cooperations.
The differential is the actual unit-corrected coproduct followed by
the actual tensor boundary, not an independently assumed polynomial map. -/
theorem sphereH6DoubleInternalE2_eq_zero_iff_cooperation_cobar
    (hK : Mod2KunnethSuspensionCompatible H R K)
    (hD : Mod2KunnethDiagonalCompatible H R K)
    (hU : Mod2KunnethUnitCompatible H R K)
    (hM : Mod2MilnorCoproductCompatible H R K B)
    (a : Mod2Cooperations H 64) (ha : cooperationMilnorPolynomial H R B 64 a = h6Polynomial)
    (x : Mod2Homology H 0 SphereSpectrum) :
    letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
      fun i => mod2HomologyModule H R i H.HF2
    letI : Module (ZMod 2) (Mod2Homology H 63 (adamsTower H.unit SphereSpectrum 1)) :=
      mod2HomologyModule H R 63 (adamsTower H.unit SphereSpectrum 1)
    sphereH6DoubleInternalE2 H R K B hK hD hU hM a ha x = 0 ↔
      ∃ b : Mod2Cooperations H 128,
        cooperationTensorLowerMap H R
          (cooperationTensor H R (fun i => mod2HomologyF2 H R i SphereSpectrum))
          (fun i => mod2HomologyF2 H R i (adamsTower H.unit SphereSpectrum 1))
          (adamsTensorBoundary H R K SphereSpectrum) 128
          (gradedTensorAssoc (Mod2Cooperations H) (Mod2Cooperations H)
            (fun i => mod2HomologyF2 H R i SphereSpectrum) 128
            (DirectSum.lof (ZMod 2) ℤ _ 128
              (cooperationCobarDiagonal H R K 128 b ⊗ₜ[ZMod 2]
                (sphereHomologyScalarEquiv H R (128 - 128) (by decide)).symm 1))) =
        DirectSum.lof (ZMod 2) ℤ _ 64
          (a ⊗ₜ[ZMod 2] (sphereH6TensorRepresentative H R K a x :
            mod2HomologyF2 H R 63 (adamsTower H.unit SphereSpectrum 1))) := by
  letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  letI : Module (ZMod 2) (Mod2Homology H 63 (adamsTower H.unit SphereSpectrum 1)) :=
    mod2HomologyModule H R 63 (adamsTower H.unit SphereSpectrum 1)
  rw [sphereH6DoubleInternalE2_eq_zero_iff_cobar H R K B hK hD hU hM a ha x]
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨b, hb, _⟩ := sphereCooperationTensor_existsUnique H R 128 w
    refine ⟨b, ?_⟩
    rw [← hb, cooperationTensorCobarSplit_lof_tmul] at hw
    exact hw
  · rintro ⟨b, hb⟩
    refine ⟨(sphereCooperationTensorEquiv H R 128).symm b, ?_⟩
    rw [sphereCooperationTensorEquiv_symm_apply, cooperationTensorCobarSplit_lof_tmul]
    exact hb

end
end KIP126.Classical.Adams
