module

public import Mathlib.Algebra.DirectSum.Basic

@[expose] public section

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
