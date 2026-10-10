import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Tensor.Proofs
import Mathlib.LinearAlgebra.Dual.Lemmas

namespace KIP126.StableHomotopy.Cohomology

noncomputable section

open CategoryTheory KIP126.Core.Algebra
open scoped TensorProduct DirectSum

universe u v w

variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  (V : ℤ → Type w) [∀ i, AddCommGroup (V i)] [∀ i, Module (ZMod 2) (V i)]

/-- In a nonzero cooperation degree, the elementary tensor has zero
augmentation because the actual coefficient group π_k H vanishes. -/
theorem cooperationTensorAugmentation_lof_tmul_eq_zero (n k : ℤ) (hk : k ≠ 0)
    (a : Mod2Cooperations H k) (x : V (n - k)) :
    letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
      fun i => mod2HomologyModule H R i H.HF2
    cooperationTensorAugmentation H R V n
      (DirectSum.lof (ZMod 2) ℤ _ k (a ⊗ₜ[ZMod 2] x)) = 0 := by
  letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  letI : ∀ i, Module (ZMod 2) (HomotopyGroup i H.HF2) :=
    fun i => mod2HF2HomotopyModule H R i
  simp only [cooperationTensorAugmentation, LinearMap.comp_apply,
    cooperationTensorCounit, gradedTensorMap_lof_tmul,
    cooperationCounitF2_eq_zero_of_ne H R k hk, LinearMap.zero_apply,
    TensorProduct.zero_tmul, map_zero]

/-- Nonzero pure tensors remain nonzero in their total-degree direct sum.
This uses only vector-space separation over F₂, not a Milnor basis. -/
theorem cooperationTensor_lof_tmul_ne_zero (n k : ℤ)
    (a : Mod2Cooperations H k) (ha : a ≠ 0) (x : V (n - k)) (hx : x ≠ 0) :
    letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
      fun i => mod2HomologyModule H R i H.HF2
    DirectSum.lof (ZMod 2) ℤ (fun i => Mod2Cooperations H i ⊗[ZMod 2] V (n - i)) k
      (a ⊗ₜ[ZMod 2] x) ≠ 0 := by
  letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) ha
  intro hz
  have ht : a ⊗ₜ[ZMod 2] x = 0 := by
    have h := congrArg (fun z => z k) hz
    rw [DirectSum.lof_apply] at h
    exact h
  have h := congrArg
    (fun z => TensorProduct.lid (ZMod 2) (V (n - k)) ((f.rTensor (V (n - k))) z)) ht
  apply hx
  simpa [hf] using h

end

end KIP126.StableHomotopy.Cohomology
