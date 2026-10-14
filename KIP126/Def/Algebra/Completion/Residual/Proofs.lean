module

public import KIP126.Def.Algebra.Completion.Sequential.Proofs
public import KIP126.Def.Algebra.InverseSequence.Completion.Proofs

@[expose] public section

namespace KIP126.Core.Algebra.Filtration.CompletionWitness
open CategoryTheory CategoryTheory.Limits
universe u v w z
variable {R : Type u} [Ring R]
variable {ι : Type w} {A : CategoryTheory.GradedObject ι (ModuleCat.{v} R)}

/-- A residual sequence whose `1 - shift` is bijective and whose projection
kernels are finite makes its actual image filtration complete. The
canonical quotient projections must have precisely these residual images
as kernels; no replacement filtration or abutment is selected. -/
noncomputable def of_residual_sequence (F : Filtration A) (i : ι)
    {B : ℕ → Type z} [∀ n, AddCommGroup (B n)]
    (p : ∀ n, B n →+ A i) (f : ∀ n, B (n + 1) →+ B n)
    (hp : ∀ n b, p n (f n b) = p (n + 1) b)
    (hbij : Function.Bijective (fun x : ∀ n, B n => fun n => x n - f n (x (n + 1))))
    (hker : ∀ n : ℕ, ∀ a : A i,
      F.quotientProjection (n : ℤ) i a = 0 ↔ ∃ b, p n b = a)
    [∀ n, Finite (p n).ker] : CompletionWitness F i := by
  classical
  apply of_unique_nat_module_lifts F i
  intro q hq
  have hs (n : ℕ) : Function.Surjective (F.quotientProjection (n : ℤ) i) := by
    apply (ModuleCat.epi_iff_surjective _).mp
    change Epi (cokernel.π (F.F (n : ℤ) i).arrow)
    infer_instance
  choose a ha using fun n => hs n (q n)
  have hadiff (n : ℕ) : ∃ b, p n b = a (n + 1) - a n := by
    apply (hker n _).mp
    rw [map_sub, ha n, sub_eq_zero]
    rw [← hq n, ← ha (n + 1)]
    exact (congrArg (fun g : A i ⟶ F.quotientAt (n : ℤ) i => g (a (n + 1)))
      (F.quotientProjection_transition (show (n : ℤ) ≤ (n + 1 : ℕ) by omega) i)).symm
  obtain ⟨x, hx⟩ := InverseSequence.exists_limit_of_surjective_sub_shift p f hp hbij.2 a hadiff
  have hxq (n : ℕ) : F.quotientProjection (n : ℤ) i x = q n := by
    obtain ⟨b, hb⟩ := hx n
    apply sub_eq_zero.mp
    rw [← ha n, ← map_sub, ← hb]
    exact (hker n _).mpr ⟨b, rfl⟩
  refine ⟨x, hxq, fun y hy => ?_⟩
  apply sub_eq_zero.mp
  apply InverseSequence.eq_zero_of_mem_ranges_of_injective_sub_shift p f hp hbij.1
  intro n
  apply (hker n _).mp
  rw [map_sub, hy n, hxq n, sub_self]

end KIP126.Core.Algebra.Filtration.CompletionWitness
