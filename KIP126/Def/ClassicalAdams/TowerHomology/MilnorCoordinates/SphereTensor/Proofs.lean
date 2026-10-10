import KIP126.Def.ClassicalAdams.TowerHomology.MilnorCoordinates.SphereTensor.Data
import KIP126.Def.ClassicalAdams.TowerHomology.MilnorCoordinates.H6.Data

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology KIP126.Steenrod.Milnor KIP126.Core.Algebra
open scoped TensorProduct DirectSum

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)

/-- The scalar normalization uses precisely the already chosen sphere unit. -/
theorem sphereHomologyScalarEquiv_symm_one :
    (sphereHomologyScalarEquiv H R 0 rfl).symm 1 = sphereMilnorUnitCoefficient H R := by
  rfl

/-- The normalized sphere coefficient is unchanged by a displayed degree cast. -/
theorem sphereHomologyScalarEquiv_cast_symm_one (n m : ℤ) (hn : n = 0) (hm : m = 0)
    (h : n = m) :
    LinearEquiv.cast (R := ZMod 2) (M := fun i => mod2HomologyF2 H R i SphereSpectrum) h
      ((sphereHomologyScalarEquiv H R n hn).symm 1) =
      (sphereHomologyScalarEquiv H R m hm).symm 1 := by
  subst m
  subst n
  rfl

/-- The inverse coefficient-removal map inserts the unique normalized
sphere coefficient into the summand of cooperation degree n. -/
theorem sphereCooperationTensorEquiv_symm_apply (n : ℤ) (a : Mod2Cooperations H n) :
    letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
      fun i => mod2HomologyModule H R i H.HF2
    (sphereCooperationTensorEquiv H R n).symm a =
      DirectSum.lof (ZMod 2) ℤ _ n
        (a ⊗ₜ[ZMod 2] (sphereHomologyScalarEquiv H R (n - n) (sub_self n)).symm 1) := by
  letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  simp [sphereCooperationTensorEquiv, directSumConcentratedEquiv,
    TensorProduct.congr_symm, TensorProduct.rid_symm_apply, TensorProduct.congr_tmul]
  rfl

/-- Every candidate tensor source has a unique actual cooperation coefficient.
No assumption about its first differential is needed. -/
theorem sphereCooperationTensor_existsUnique (n : ℤ)
    (w : cooperationTensor H R (fun i => mod2HomologyF2 H R i SphereSpectrum) n) :
    letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
      fun i => mod2HomologyModule H R i H.HF2
    ∃! a : Mod2Cooperations H n,
      DirectSum.lof (ZMod 2) ℤ _ n
        (a ⊗ₜ[ZMod 2] (sphereHomologyScalarEquiv H R (n - n) (sub_self n)).symm 1) = w := by
  letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  simp only [← sphereCooperationTensorEquiv_symm_apply]
  exact (sphereCooperationTensorEquiv H R n).symm.bijective.existsUnique w

end
end KIP126.Classical.Adams
