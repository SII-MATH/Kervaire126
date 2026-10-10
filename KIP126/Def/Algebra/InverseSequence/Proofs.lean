import Mathlib.Data.Nat.Init
import Mathlib.Logic.Function.Defs

namespace KIP126.Core.InverseSequence

universe u

/-- Surjective adjacent maps extend one specified point to a compatible
dependent inverse sequence. No nonemptiness of the other fibers is assumed. -/
theorem exists_compatible_of_surjective (m₀ : ℕ)
    (A : (m : ℕ) → m₀ ≤ m → Type u)
    (restrict : ∀ (m : ℕ) (hm : m₀ ≤ m),
      A (m + 1) (Nat.le_succ_of_le hm) → A m hm)
    (hsurj : ∀ (m : ℕ) (hm : m₀ ≤ m), Function.Surjective (restrict m hm))
    (a₀ : A m₀ (Nat.le_refl m₀)) :
    ∃ a : ∀ (m : ℕ) (hm : m₀ ≤ m), A m hm,
      a m₀ (Nat.le_refl m₀) = a₀ ∧
        ∀ (m : ℕ) (hm : m₀ ≤ m),
          restrict m hm (a (m + 1) (Nat.le_succ_of_le hm)) = a m hm := by
  classical
  let next : ∀ {m : ℕ} (hm : m₀ ≤ m), A m hm → A (m + 1) (Nat.le_succ_of_le hm) :=
    fun {m} hm a => (hsurj m hm a).choose
  let a : ∀ (m : ℕ) (hm : m₀ ≤ m), A m hm :=
    fun m hm => Nat.leRec (motive := A) a₀ (@next) hm
  refine ⟨a, Nat.leRec_self a₀ (@next), ?_⟩
  intro m hm
  dsimp only [a]
  rw [Nat.leRec_succ a₀ (@next) hm]
  exact (hsurj m hm _).choose_spec

end KIP126.Core.InverseSequence
