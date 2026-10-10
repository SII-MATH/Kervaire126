import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Kunneth.Diagonal.Cobar.Data
import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Kunneth.Diagonal.Primitive.Proofs

namespace KIP126.StableHomotopy.Cohomology

noncomputable section
open CategoryTheory KIP126.Core.Algebra
open scoped TensorProduct DirectSum

universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  (K : Mod2CooperationKunneth H R)
  (V : ℤ → Type w) [∀ i, AddCommGroup (V i)] [∀ i, Module (ZMod 2) (V i)]

/-- Reassociate the two unit parts of a cooperation tensor explicitly. -/
theorem cooperationTensor_unitParts (n k : ℤ) (a : Mod2Cooperations H k) (x : V (n - k)) :
    letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
      fun i => mod2HomologyModule H R i H.HF2
    gradedTensorAssoc (Mod2Cooperations H) (Mod2Cooperations H) V n
      (DirectSum.lof (ZMod 2) ℤ _ k
        ((cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i H.HF2) k a +
          cooperationTensorRightUnit H R k a) ⊗ₜ[ZMod 2] x)) =
      cooperationTensorUnit H R (cooperationTensor H R V) n
        (DirectSum.lof (ZMod 2) ℤ _ k (a ⊗ₜ[ZMod 2] x)) +
      cooperationTensorMap H R V (cooperationTensorUnit H R V) n
        (DirectSum.lof (ZMod 2) ℤ _ k (a ⊗ₜ[ZMod 2] x)) := by
  letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  erw [TensorProduct.add_tmul, map_add, map_add]
  simp only [cooperationTensorUnit, cooperationTensorRightUnit, cooperationTensorMap,
    gradedTensorMapRight, LinearMap.comp_apply,
    TensorProduct.mk_apply, LinearMap.lTensor_tmul, DirectSum.lmap_lof]
  erw [gradedTensorAssoc_lof_tmul, gradedTensorAssoc_lof_tmul]
  have hl := cooperationTensor_lof_cast H R V n (n - 0) k (k - 0) (n - k)
    (sub_zero n).symm (sub_zero k).symm rfl (by omega) a x
  have hr := cooperationTensor_lof_cast H R V (n - k) (n - k) 0 (k - k) (n - k)
    rfl (sub_self k).symm (sub_zero (n - k)).symm (by omega) (cooperationUnit H) x
  erw [← hl, ← hr]
  rfl

/-- The split operation really acts by the unit-corrected coproduct of
the first factor, rather than a new independently specified operation. -/
theorem cooperationTensorCobarSplit_lof_tmul (n k : ℤ)
    (a : Mod2Cooperations H k) (x : V (n - k)) :
    letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
      fun i => mod2HomologyModule H R i H.HF2
    cooperationTensorCobarSplit H R K V n
      (DirectSum.lof (ZMod 2) ℤ _ k (a ⊗ₜ[ZMod 2] x)) =
      gradedTensorAssoc (Mod2Cooperations H) (Mod2Cooperations H) V n
        (DirectSum.lof (ZMod 2) ℤ _ k
          (cooperationCobarDiagonal H R K k a ⊗ₜ[ZMod 2] x)) := by
  letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  simp only [cooperationTensorCobarSplit, cooperationCobarDiagonal,
    LinearMap.sub_apply, LinearMap.add_apply]
  erw [TensorProduct.sub_tmul, map_sub, map_sub]
  erw [cooperationTensor_unitParts H R V n k a x]
  congr 1
  change gradedTensorAssoc (Mod2Cooperations H) (Mod2Cooperations H) V n
    (gradedTensorMap (cooperationTensorDiagonal H R K) V n
      (DirectSum.lof (ZMod 2) ℤ _ k (a ⊗ₜ[ZMod 2] x))) = _
  exact congrArg (gradedTensorAssoc (Mod2Cooperations H) (Mod2Cooperations H) V n)
    (gradedTensorMap_lof_tmul (cooperationTensorDiagonal H R K) V n k a x)

end
end KIP126.StableHomotopy.Cohomology
