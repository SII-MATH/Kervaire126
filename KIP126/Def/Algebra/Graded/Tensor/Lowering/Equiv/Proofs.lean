import KIP126.Def.Algebra.Graded.Tensor.Lowering.Equiv.Data
import KIP126.Def.Algebra.Graded.Tensor.Lowering.Proofs

namespace KIP126.Core.Algebra

noncomputable section
open scoped TensorProduct DirectSum
variable {R : Type*} [CommRing R]
  (A : ℤ → Type*) [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
  {V W : ℤ → Type*} [∀ i, AddCommGroup (V i)] [∀ i, AddCommGroup (W i)]
  [∀ i, Module R (V i)] [∀ i, Module R (W i)]

theorem gradedTensorLowerEquiv_toLinearMap (e : ∀ i, V i ≃ₗ[R] W (i - 1)) (n : ℤ) :
    (gradedTensorLowerEquiv A e n).toLinearMap =
      gradedTensorLowerMap A (fun i => (e i).toLinearMap) n := by
  ext i a x
  simp [gradedTensorLowerEquiv, DirectSum.coe_congrLinearEquiv,
    gradedTensorLowerMap]

theorem gradedTensorLowerMap_injective (g : ∀ i, V i →ₗ[R] W (i - 1))
    (hg : ∀ i, Function.Injective (g i)) (n : ℤ) [∀ i, Module.Flat R (A i)] :
    Function.Injective (gradedTensorLowerMap A g n) := by
  apply (DirectSum.lmap_injective _).mpr
  intro i
  apply Module.Flat.lTensor_preserves_injective_linearMap
  exact (LinearEquiv.cast (R := R) (M := W)
    (show n - i - 1 = n - 1 - i by omega)).injective.comp (hg (n - i))

end
end KIP126.Core.Algebra
