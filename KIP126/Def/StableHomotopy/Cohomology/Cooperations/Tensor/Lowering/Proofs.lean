import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Tensor.Lowering.Data

namespace KIP126.StableHomotopy.Cohomology

noncomputable section

open CategoryTheory KIP126.Core.Algebra

universe u v w

variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)

theorem cooperationTensorLowerMap_comp (V W U : ℤ → Type w)
    [∀ i, AddCommGroup (V i)] [∀ i, AddCommGroup (W i)] [∀ i, AddCommGroup (U i)]
    [∀ i, Module (ZMod 2) (V i)] [∀ i, Module (ZMod 2) (W i)] [∀ i, Module (ZMod 2) (U i)]
    (f : ∀ i, V i →ₗ[ZMod 2] W i) (g : ∀ i, W i →ₗ[ZMod 2] U (i - 1)) (n : ℤ) :
    (cooperationTensorLowerMap H R W U g n).comp (cooperationTensorMap H R V f n) =
      cooperationTensorLowerMap H R V U (fun i => (g i).comp (f i)) n := by
  letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) := fun i => mod2HomologyModule H R i H.HF2
  exact gradedTensorLowerMap_comp (Mod2Cooperations H) f g n

end

end KIP126.StableHomotopy.Cohomology
