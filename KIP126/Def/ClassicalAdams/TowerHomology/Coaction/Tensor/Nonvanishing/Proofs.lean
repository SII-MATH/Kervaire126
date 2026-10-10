import KIP126.Def.ClassicalAdams.TowerHomology.Coaction.Tensor.Proofs
import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Tensor.Nonvanishing.Proofs

namespace KIP126.Classical.Adams

noncomputable section

open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology
open scoped TensorProduct DirectSum

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C))
  (R : Mod2RingStructure H) (K : Mod2CooperationKunneth H R)
  [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]

/-- On augmentation-zero tensors the actual boundary detects zero exactly.
This follows from normalization, without unit, diagonal, or suspension
compatibility assumptions on the Künneth map. -/
theorem adamsTensorBoundary_eq_zero_iff_of_augmentation_eq_zero (X : C) (n : ℤ)
    (w : cooperationTensor H R (fun i => mod2HomologyF2 H R i X) n)
    (hw : cooperationTensorAugmentation H R (fun i => mod2HomologyF2 H R i X) n w = 0) :
    adamsTensorBoundary H R K X n w = 0 ↔ w = 0 := by
  constructor
  · intro hq
    have h := adamsTensorBoundary_normalization H R K X n w
    rw [hw, map_zero, sub_zero] at h
    rw [hq] at h
    erw [map_zero, map_zero] at h
    exact h.symm
  · rintro rfl
    exact (adamsTensorBoundary H R K X n).map_zero

/-- In nonzero cooperation degree, the boundary of a tensor of nonzero
classes is nonzero in the actual next fiber's homology. -/
theorem adamsTensorBoundary_lof_tmul_ne_zero (X : C) (n k : ℤ) (hk : k ≠ 0)
    (a : Mod2Cooperations H k) (ha : a ≠ 0)
    (x : Mod2Homology H (n - k) X) (hx : x ≠ 0) :
    letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
      fun i => mod2HomologyModule H R i H.HF2
    adamsTensorBoundary H R K X n
      (DirectSum.lof (ZMod 2) ℤ _ k (a ⊗ₜ[ZMod 2] x)) ≠ 0 := by
  letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  rw [ne_eq, adamsTensorBoundary_eq_zero_iff_of_augmentation_eq_zero H R K X n _
    (cooperationTensorAugmentation_lof_tmul_eq_zero H R _ n k hk a x)]
  exact cooperationTensor_lof_tmul_ne_zero H R (fun i => mod2HomologyF2 H R i X)
    n k a ha x hx

/-- The original first-page isomorphism preserves this nonvanishing on the
sphere's first nontrivial tower stage. -/
theorem sphereAdamsPageOne_tensorBoundary_ne_zero (n k : ℤ) (hk : k ≠ 0)
    (a : Mod2Cooperations H k) (ha : a ≠ 0)
    (x : Mod2Homology H (n - k) SphereSpectrum) (hx : x ≠ 0) :
    letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
      fun i => mod2HomologyModule H R i H.HF2
    (adamsPageOneHomologyEquiv H.unit SphereSpectrum 1 n).symm
      (adamsTensorBoundary H R K SphereSpectrum n
        (DirectSum.lof (ZMod 2) ℤ _ k (a ⊗ₜ[ZMod 2] x))) ≠ 0 := by
  letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  intro hz
  have h := congrArg (adamsPageOneHomologyEquiv H.unit SphereSpectrum 1 n) hz
  rw [LinearEquiv.apply_symm_apply, map_zero] at h
  exact adamsTensorBoundary_lof_tmul_ne_zero H R K SphereSpectrum n k hk a ha x hx h

end

end KIP126.Classical.Adams
