module

public import KIP126.Def.StableHomotopy.Implementation.HF2.Finiteness.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Product.Abelian.Data
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open scoped BigOperators

/-- Finite products of the actual coefficient shifts have finite original
stable homotopy groups. -/
theorem SourceHF2Model.shiftProduct_stableHomotopy_finite (M : SourceHF2Model)
    {J : Type} [Finite J] (s : J → ℤ) (d : ℤ) :
    Finite (Prespectrum.StableHomotopy
      (Prespectrum.piPrespectrum (fun j => M.shiftSpectrum (s j))) d) := by
  letI : ∀ j, Finite ((M.shiftSpectrum (s j)).StableHomotopy d) :=
    fun j => M.shiftStableHomotopy_finite (s j) d
  exact Finite.of_equiv _ (Prespectrum.stablePiAddEquiv _ d).symm.toEquiv

/-- A degree absent from a finite family of coefficient shifts vanishes
in their actual pointwise product. -/
theorem SourceHF2Model.shiftProduct_stableHomotopy_vanishes (M : SourceHF2Model)
    {J : Type} [Finite J] (s : J → ℤ) (d : ℤ) (h : ∀ j, d ≠ s j) :
    Subsingleton (Prespectrum.StableHomotopy
      (Prespectrum.piPrespectrum (fun j => M.shiftSpectrum (s j))) d) := by
  letI : ∀ j, Subsingleton ((M.shiftSpectrum (s j)).StableHomotopy d) :=
    fun j => M.shiftStableHomotopy_vanishes (s j) d (h j)
  exact (Prespectrum.stablePiAddEquiv _ d).injective.subsingleton

/-- The exact cardinality follows from the actual finite-product comparison
and the original coefficient calculation in each degree. -/
theorem SourceHF2Model.shiftProduct_stableHomotopy_card (M : SourceHF2Model)
    {J : Type} [Fintype J] (s : J → ℤ) (d : ℤ) :
    Nat.card (Prespectrum.StableHomotopy
      (Prespectrum.piPrespectrum (fun j => M.shiftSpectrum (s j))) d) =
      ∏ j, if d = s j then 2 else 1 := by
  letI : ∀ j, Finite ((M.shiftSpectrum (s j)).StableHomotopy d) :=
    fun j => M.shiftStableHomotopy_finite (s j) d
  rw [Nat.card_congr (Prespectrum.stablePiAddEquiv _ d).toEquiv, Nat.card_pi]
  exact Finset.prod_congr rfl (fun j _ => M.shiftStableHomotopy_card (s j) d)

end KIP126.StableHomotopy.Implementation
