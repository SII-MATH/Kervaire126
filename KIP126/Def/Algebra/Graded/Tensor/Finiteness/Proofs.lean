module

public import KIP126.Def.Algebra.Graded.Tensor.Data
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.Data.Int.Interval

@[expose] public section

namespace KIP126.Core.Algebra

open scoped TensorProduct DirectSum

variable {R : Type*} [CommRing R]
  (A V : ℤ → Type*) [∀ i, AddCommGroup (A i)] [∀ i, AddCommGroup (V i)]
  [∀ i, Module R (A i)] [∀ i, Module R (V i)]

/-- Below the sum of the two bounds, every homogeneous tensor summand vanishes. -/
theorem gradedTensor_subsingleton_of_lt (a b n : ℤ)
    (hA : ∀ i, i < a → Subsingleton (A i))
    (hV : ∀ i, i < b → Subsingleton (V i)) (hn : n < a + b) :
    Subsingleton (gradedTensor R A V n) := by
  refine ⟨fun x y => ?_⟩
  apply DFinsupp.ext
  intro i
  by_cases hi : i < a
  · letI := hA i hi
    exact Subsingleton.elim _ _
  · letI := hV (n-i) (by omega)
    exact Subsingleton.elim _ _

/-- A homogeneous Cauchy tensor degree is finite when both graded factors
are degreewise finite and bounded below over a finite coefficient ring. -/
theorem gradedTensor_finite [Finite R] (a b n : ℤ)
    (hA : ∀ i, i < a → Subsingleton (A i))
    (hV : ∀ i, i < b → Subsingleton (V i))
    (fA : ∀ i, Finite (A i)) (fV : ∀ i, Finite (V i)) :
    Finite (gradedTensor R A V n) := by
  classical
  let I := Set.Icc a (n-b)
  letI := (Set.finite_Icc a (n-b)).fintype
  have hf (i : ℤ) : Finite (A i ⊗[R] V (n-i)) := by
    letI := fA i
    letI := fV (n-i)
    letI : Module.Finite R (A i) := Module.Finite.of_finite
    letI : Module.Finite R (V (n-i)) := Module.Finite.of_finite
    exact Module.finite_of_finite R
  letI (i : I) : Finite (A i.val ⊗[R] V (n-i.val)) := hf i.val
  let f : gradedTensor R A V n → (∀ i : I, A i.val ⊗[R] V (n-i.val)) :=
    fun x i => x i.val
  apply Finite.of_injective f
  intro x y h
  apply DFinsupp.ext
  intro i
  by_cases hi : i ∈ I
  · exact congrFun h ⟨i, hi⟩
  · by_cases hil : i < a
    · letI := hA i hil
      exact Subsingleton.elim _ _
    · have hiv : n-i < b := by
        change ¬ (a ≤ i ∧ i ≤ n-b) at hi
        omega
      letI := hV (n-i) hiv
      exact Subsingleton.elim _ _

end KIP126.Core.Algebra
