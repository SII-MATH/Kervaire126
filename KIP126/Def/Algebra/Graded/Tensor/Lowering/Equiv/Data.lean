import KIP126.Def.Algebra.Graded.Tensor.Lowering.Data

namespace KIP126.Core.Algebra

noncomputable section
variable {R : Type*} [CommRing R]
  (A : ℤ → Type*) [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
  {V W : ℤ → Type*} [∀ i, AddCommGroup (V i)] [∀ i, AddCommGroup (W i)]
  [∀ i, Module R (V i)] [∀ i, Module R (W i)]

/-- Tensor a degree-minus-one equivalence with an unchanged left factor. -/
def gradedTensorLowerEquiv (e : ∀ i, V i ≃ₗ[R] W (i - 1)) (n : ℤ) :
    gradedTensor R A V n ≃ₗ[R] gradedTensor R A W (n - 1) :=
  DirectSum.congrLinearEquiv fun i =>
    TensorProduct.congr (LinearEquiv.refl R (A i))
      ((e (n - i)).trans
        (LinearEquiv.cast (R := R) (M := W) (show n - i - 1 = n - 1 - i by omega)))

end
end KIP126.Core.Algebra
