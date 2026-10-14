module

public import KIP126.Def.StableHomotopy.Implementation.Completion.Locality.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.SourceShift.Integer.Coherence.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation
open CategoryTheory KIP126.Foundation
set_option backward.isDefEq.respectTransparency false

/-- All original coherent integer shifts of a local object are local. -/
theorem SourceIsHF2Local.shift {X : SourceCategory.{0}}
    (hX : SourceIsHF2Local X) (d : ℤ) : SourceIsHF2Local (X⟦d⟧) := by
  have hs : ∀ n : ℕ, SourceIsHF2Local
      ((functorIterate Prespectrum.sourceSuspensionFunctor n).obj X) := by
    intro n
    induction n with
    | zero => exact @hX
    | succ n ih => exact @SourceIsHF2Local.suspension _ @ih
  have ht : ∀ n : ℕ, SourceIsHF2Local
      ((functorIterate Prespectrum.sourceDesuspensionFunctor n).obj X) := by
    intro n
    induction n with
    | zero => exact @hX
    | succ n ih => exact @SourceIsHF2Local.desuspension _ @ih
  cases d with
  | ofNat n => exact @hs n
  | negSucc n => exact @ht (n+1)

end KIP126.StableHomotopy.Implementation
