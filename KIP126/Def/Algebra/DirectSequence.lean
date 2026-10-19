module

public import Mathlib.Algebra.DirectSum.Basic

@[expose] public section

section

namespace KIP126.Foundation

open scoped DirectSum

universe u

variable {A : ℕ → Type u} [∀ n, AddCommGroup (A n)]

/-- The actual forward shift on the algebraic direct sum of a sequence
of abelian groups, using its specified adjacent homomorphisms. -/
def directSequenceShift (f : ∀ n, A n →+ A (n+1)) :
    (⨁ n, A n) →+ ⨁ n, A n :=
  DirectSum.toAddMonoid (fun n => (DirectSum.of A (n+1)).comp (f n))

/-- The actual difference homomorphism presenting the sequential colimit. -/
def directSequenceOneSubShift (f : ∀ n, A n →+ A (n+1)) :
    (⨁ n, A n) →+ ⨁ n, A n :=
  AddMonoidHom.id _ - directSequenceShift f

end KIP126.Foundation

end

section

namespace KIP126.Foundation

open scoped DirectSum

universe u

variable {A : ℕ → Type u} [∀ n, AddCommGroup (A n)]

/-- The actual forward shift has zero initial coordinate. -/
@[simp] theorem directSequenceShift_zero (f : ∀ n, A n →+ A (n+1)) (x : ⨁ n, A n) :
    directSequenceShift f x 0 = 0 := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i x =>
    rw [directSequenceShift, DirectSum.toAddMonoid_of, AddMonoidHom.comp_apply]
    exact DirectSum.of_eq_of_ne _ _ _ (by simp)
  | add x y hx hy => simp only [map_add, DirectSum.add_apply, hx, hy, add_zero]

/-- Every successor coordinate of the actual shift is the specified
transition applied to the preceding coordinate. -/
@[simp] theorem directSequenceShift_succ (f : ∀ n, A n →+ A (n+1))
    (x : ⨁ n, A n) (n : ℕ) : directSequenceShift f x (n+1) = f n (x n) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i x =>
    rw [directSequenceShift, DirectSum.toAddMonoid_of, AddMonoidHom.comp_apply]
    by_cases h : n = i
    · subst n
      simp only [DirectSum.of_eq_same]
    · rw [DirectSum.of_eq_of_ne _ _ _ (fun hni => h (Nat.succ.inj hni)),
        DirectSum.of_eq_of_ne _ _ _ h, map_zero]
  | add x y hx hy => simp only [map_add, DirectSum.add_apply, hx, hy]

/-- The actual Milnor difference on a direct sum is injective for every
sequence of abelian groups and arbitrary transition homomorphisms. -/
theorem directSequenceOneSubShift_injective (f : ∀ n, A n →+ A (n+1)) :
    Function.Injective (directSequenceOneSubShift f) := by
  have hker (x : ⨁ n, A n) (hx : directSequenceOneSubShift f x = 0) : x = 0 := by
    change x - directSequenceShift f x = 0 at hx
    have he := sub_eq_zero.mp hx
    ext n
    change x n = 0
    induction n with
    | zero => exact (DFunLike.congr_fun he 0).trans (directSequenceShift_zero f x)
    | succ n hn =>
      calc
        x (n+1) = directSequenceShift f x (n+1) := DFunLike.congr_fun he (n+1)
        _ = f n (x n) := directSequenceShift_succ f x n
        _ = 0 := by rw [hn, map_zero]
  intro x y h
  apply sub_eq_zero.mp
  apply hker
  rw [map_sub, h, sub_self]

end KIP126.Foundation

end
