module

public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Tactic.Abel

@[expose] public section

namespace KIP126.Core.InverseSequence

variable (G : ℕ → Type*) [∀ n, AddCommGroup (G n)]
  (f : ∀ n, G (n + 1) →+ G n)

/-- Successively choose lifts to solve the difference equation in a
surjective inverse sequence. -/
theorem surjective_sub_shift_of_surjective
    (hf : ∀ n, Function.Surjective (f n)) :
    Function.Surjective (fun x : ∀ n, G n => fun n => x n - f n (x (n + 1))) := by
  classical
  intro b
  let a : ∀ n, G n := fun n =>
    Nat.rec (motive := fun n => G n) 0
      (fun n x => (hf n (x - b n)).choose) n
  refine ⟨a, funext fun n => ?_⟩
  have h : f n (a (n + 1)) = a n - b n := (hf n (a n - b n)).choose_spec
  change a n - f n (a (n + 1)) = b n
  rw [h]
  abel

end KIP126.Core.InverseSequence
