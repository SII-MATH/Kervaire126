import Mathlib.Data.Nat.Init
import Mathlib.Data.Finite.Prod
import Mathlib.Order.KonigLemma

namespace KIP126.Core.InverseSequence

universe u

/-- Nonempty finite terms with arbitrary adjacent restriction maps admit a
compatible dependent inverse sequence. The point at the initial index is
not prescribed, and the restriction maps need not be surjective. -/
theorem exists_compatible_of_finite (m₀ : ℕ)
    (A : (m : ℕ) → m₀ ≤ m → Type u)
    (restrict : ∀ (m : ℕ) (hm : m₀ ≤ m),
      A (m + 1) (Nat.le_succ_of_le hm) → A m hm)
    (hfinite : ∀ (m : ℕ) (hm : m₀ ≤ m), Finite (A m hm))
    (hne : ∀ (m : ℕ) (hm : m₀ ≤ m), Nonempty (A m hm)) :
    ∃ a : ∀ (m : ℕ) (hm : m₀ ≤ m), A m hm,
      ∀ (m : ℕ) (hm : m₀ ≤ m),
        restrict m hm (a (m + 1) (Nat.le_succ_of_le hm)) = a m hm := by
  classical
  let B (m : ℕ) := ∀ hm : m₀ ≤ m, A m hm
  let step (m : ℕ) (b : B (m + 1)) : B m :=
    fun hm => restrict m hm (b (Nat.le_succ_of_le hm))
  letI : ∀ m, Finite (B m) := fun m => by
    letI : ∀ hm : m₀ ≤ m, Finite (A m hm) := hfinite m
    exact Pi.finite
  letI : ∀ m, Nonempty (B m) :=
    fun m => ⟨fun hm => Classical.choice (hne m hm)⟩
  let π : {i j : ℕ} → i ≤ j → B j → B i :=
    fun {_ _} hij b => Nat.decreasingInduction (fun k _ => step k) b hij
  obtain ⟨a, ha⟩ := exists_seq_forall_proj_of_forall_finite π
    (fun {_} _ => Nat.decreasingInduction_self _ _)
    (by
      intro i j k hij hjk b
      exact (Nat.decreasingInduction_trans (motive := fun m (_ : m ≤ k) => B m)
        hij hjk (fun m _ => step m) b).symm)
    (fun _ _ => Set.toFinite _)
  refine ⟨fun m hm => a m hm, ?_⟩
  intro m hm
  have h := congrFun (ha (Nat.le_succ m)) hm
  simpa only [π, Nat.decreasingInduction_succ', step] using h

end KIP126.Core.InverseSequence
