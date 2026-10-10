import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Kunneth.Diagonal.Proofs
import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Unit.Right.Data
import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Unit.Proofs

namespace KIP126.StableHomotopy.Cohomology

noncomputable section

open CategoryTheory KIP126.Core.Algebra
open scoped TensorProduct DirectSum

universe u v w

variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  (K : Mod2CooperationKunneth H R)
  (V : ℤ → Type w) [∀ i, AddCommGroup (V i)] [∀ i, Module (ZMod 2) (V i)]

/-- Transport total and summand degrees of an elementary cooperation tensor. -/
theorem cooperationTensor_lof_cast (n n' k k' j : ℤ) (hn : n = n') (hk : k = k')
    (hj : j = n - k) (hj' : j = n' - k') (a : Mod2Cooperations H k) (x : V j) :
    letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
      fun i => mod2HomologyModule H R i H.HF2
    (LinearEquiv.cast (R := ZMod 2) (M := cooperationTensor H R V) hn)
      (DirectSum.lof (ZMod 2) ℤ _ k (a ⊗ₜ[ZMod 2]
        (LinearEquiv.cast (R := ZMod 2) (M := V) hj) x)) =
    DirectSum.lof (ZMod 2) ℤ _ k'
      ((LinearEquiv.cast (R := ZMod 2) (M := fun i => mod2HomologyF2 H R i H.HF2) hk) a
        ⊗ₜ[ZMod 2] (LinearEquiv.cast (R := ZMod 2) (M := V) hj') x) := by
  subst n'
  subst k'
  rfl

/-- Tensoring a primitive cooperation with a coefficient class gives two
unit-insertion terms. This is an actual graded tensor identity, before
any Adams boundary or polynomial coordinates. -/
theorem cooperationTensorComultiply_primitive (n k : ℤ) (a : Mod2Cooperations H k)
    (ha : cooperationTensorDiagonal H R K k a =
      cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i H.HF2) k a +
        cooperationTensorRightUnit H R k a) (x : V (n - k)) :
    letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
      fun i => mod2HomologyModule H R i H.HF2
    let z := DirectSum.lof (ZMod 2) ℤ _ k (a ⊗ₜ[ZMod 2] x)
    cooperationTensorComultiply H R K V n z =
      cooperationTensorUnit H R (cooperationTensor H R V) n z +
        cooperationTensorMap H R V (cooperationTensorUnit H R V) n z := by
  letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  dsimp only
  rw [cooperationTensorComultiply, LinearMap.comp_apply]
  erw [gradedTensorMap_lof_tmul]
  erw [ha,
    TensorProduct.add_tmul, map_add, map_add]
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

end

end KIP126.StableHomotopy.Cohomology
