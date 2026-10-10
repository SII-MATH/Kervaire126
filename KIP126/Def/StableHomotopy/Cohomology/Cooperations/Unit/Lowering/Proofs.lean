import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Unit.Proofs
import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Tensor.Lowering.Proofs

namespace KIP126.StableHomotopy.Cohomology

noncomputable section

open CategoryTheory KIP126.Core.Algebra
open scoped TensorProduct DirectSum

universe u v w

variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  (V W : ℤ → Type w) [∀ i, AddCommGroup (V i)] [∀ i, AddCommGroup (W i)]
  [∀ i, Module (ZMod 2) (V i)] [∀ i, Module (ZMod 2) (W i)]

/-- The elementary unit tensor is natural also for degree-minus-one maps,
with the required total-degree casts. -/
theorem cooperationTensorLowerMap_unit (g : ∀ i, V i →ₗ[ZMod 2] W (i - 1))
    (n : ℤ) (x : V n) :
    cooperationTensorLowerMap H R V W g n (cooperationTensorUnit H R V n x) =
      cooperationTensorUnit H R W (n - 1) (g n x) := by
  letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  have hc (i j : ℤ) (h : i = j) (z : V i) :
      g j ((LinearEquiv.cast (R := ZMod 2) (M := V) h) z) =
        (LinearEquiv.cast (R := ZMod 2) (M := W) (congrArg (fun k => k - 1) h))
          (g i z) := by
    subst j
    rfl
  have ht (i j k : ℤ) (h : i = j) (h' : j = k) (h'' : i = k) (z : W i) :
      (LinearEquiv.cast (R := ZMod 2) (M := W) h')
        ((LinearEquiv.cast (R := ZMod 2) (M := W) h) z) =
      (LinearEquiv.cast (R := ZMod 2) (M := W) h'') z := by
    subst j
    subst k
    rfl
  simp only [cooperationTensorUnit_apply, cooperationTensorLowerMap,
    gradedTensorLowerMap_lof_tmul]
  rw [hc, ht]

end

end KIP126.StableHomotopy.Cohomology
