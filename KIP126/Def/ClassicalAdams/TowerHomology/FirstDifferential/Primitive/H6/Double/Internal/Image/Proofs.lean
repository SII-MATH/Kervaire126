import KIP126.Def.ClassicalAdams.TowerHomology.FirstDifferential.Primitive.H6.Double.Internal.Data
import KIP126.Def.ClassicalAdams.TowerHomology.FirstDifferential.CobarRecurrence.Image.Proofs
import KIP126.Def.ClassicalAdams.TowerSSData.FirstCycles.Image.Proofs

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
  (hK : Mod2KunnethSuspensionCompatible H R K)
  (hD : Mod2KunnethDiagonalCompatible H R K)
  (hU : Mod2KunnethUnitCompatible H R K)
  (hM : Mod2MilnorCoproductCompatible H R K B)
  (a : Mod2Cooperations H 64) (ha : cooperationMilnorPolynomial H R B 64 a = h6Polynomial)
  (x : Mod2Homology H 0 SphereSpectrum)

omit [(mod2UnitNatTrans H).CommShift ℤ] in
/-- The target of the image equation is the original elementary tensor.
Its degree-64 cooperation factor has zero augmentation, independently of
any Milnor coordinates or coproduct compatibility. -/
theorem sphereH6DoubleTensorRepresentative_normalized :
    letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
      fun i => mod2HomologyModule H R i H.HF2
    letI : Module (ZMod 2) (Mod2Homology H 63 (adamsTower H.unit SphereSpectrum 1)) :=
      mod2HomologyModule H R 63 (adamsTower H.unit SphereSpectrum 1)
    reducedCooperationTensorInclusion H R
      (fun i => mod2HomologyF2 H R i (adamsTower H.unit SphereSpectrum 1)) 127
      (adamsNextHomologyTensorEquiv H R K (adamsTower H.unit SphereSpectrum 1) 127
        (sphereH6DoubleTensorRepresentative H R K a x)) =
      DirectSum.lof (ZMod 2) ℤ _ 64
        (a ⊗ₜ[ZMod 2] (sphereH6TensorRepresentative H R K a x :
          mod2HomologyF2 H R 63 (adamsTower H.unit SphereSpectrum 1))) := by
  letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  letI : Module (ZMod 2) (Mod2Homology H 63 (adamsTower H.unit SphereSpectrum 1)) :=
    mod2HomologyModule H R 63 (adamsTower H.unit SphereSpectrum 1)
  unfold sphereH6DoubleTensorRepresentative
  rw [adamsTensorBoundary_normalization,
    cooperationTensorAugmentation_lof_tmul_eq_zero H R _ 127 64 (by decide),
    map_zero, sub_zero]
  rfl

/-- The actual internal double class is zero precisely when its E₁
representative is hit by d₁. This does not presume nonvanishing. -/
theorem sphereH6DoubleInternalE2_eq_zero_iff_is_differential :
    sphereH6DoubleInternalE2 H R K B hK hD hU hM a ha x = 0 ↔
      ∃ y : adamsPage H.unit SphereSpectrum 1 le_rfl 1 128,
        (adamsPageD H.unit SphereSpectrum 1 le_rfl (1, 128) (2, 128)).hom y =
          (adamsPageOneHomologyEquiv H.unit SphereSpectrum 2 128).symm
            (sphereH6DoubleTensorRepresentative H R K a x) :=
  adamsTowerE2OfFirstCycle_eq_zero_iff_is_differential H.unit SphereSpectrum 1 128 _ _

/-- Exact vanishing test for the constructed internal E₂ class, in actual
cooperation tensors. Proving that the equation has no solution would prove
nonvanishing; this theorem does not assume that calculation. -/
theorem sphereH6DoubleInternalE2_eq_zero_iff_cobar :
    letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
      fun i => mod2HomologyModule H R i H.HF2
    letI : Module (ZMod 2) (Mod2Homology H 63 (adamsTower H.unit SphereSpectrum 1)) :=
      mod2HomologyModule H R 63 (adamsTower H.unit SphereSpectrum 1)
    sphereH6DoubleInternalE2 H R K B hK hD hU hM a ha x = 0 ↔
      ∃ w : cooperationTensor H R (fun i => mod2HomologyF2 H R i SphereSpectrum) 128,
        cooperationTensorLowerMap H R
          (cooperationTensor H R (fun i => mod2HomologyF2 H R i SphereSpectrum))
          (fun i => mod2HomologyF2 H R i (adamsTower H.unit SphereSpectrum 1))
          (adamsTensorBoundary H R K SphereSpectrum) 128
          (cooperationTensorCobarSplit H R K (fun i => mod2HomologyF2 H R i SphereSpectrum) 128 w) =
        DirectSum.lof (ZMod 2) ℤ _ 64
          (a ⊗ₜ[ZMod 2] (sphereH6TensorRepresentative H R K a x :
            mod2HomologyF2 H R 63 (adamsTower H.unit SphereSpectrum 1))) := by
  letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  letI : Module (ZMod 2) (Mod2Homology H 63 (adamsTower H.unit SphereSpectrum 1)) :=
    mod2HomologyModule H R 63 (adamsTower H.unit SphereSpectrum 1)
  refine (sphereH6DoubleInternalE2_eq_zero_iff_is_differential H R K B hK hD hU hM a ha x).trans ?_
  have h :=
    sphereAdamsPageD_one_128_image_cobar_iff H R K hK hD hU
      ((adamsPageOneHomologyEquiv H.unit SphereSpectrum 2 128).symm
        (sphereH6DoubleTensorRepresentative H R K a x))
  simp only [LinearEquiv.apply_symm_apply] at h
  refine h.trans ?_
  apply exists_congr
  intro w
  rw [sphereH6DoubleTensorRepresentative_normalized]
  rfl

end
end KIP126.Classical.Adams
