module

public import KIP126.Def.StableHomotopy.Implementation.HF2.Finiteness.Data
public import KIP126.Def.StableHomotopy.Implementation.HF2.Additive.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.SourceShift.Homotopy.Proofs
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

theorem SourceHF2Model.stableHomotopy_finite (M : SourceHF2Model) (d : ℤ) :
    Finite (Prespectrum.StableHomotopy M.spectrum d) := by
  by_cases hd : d = 0
  · subst d
    exact Finite.of_equiv (ZMod 2) M.pi0.symm
  · letI := M.vanishes d hd
    infer_instance

theorem SourceHF2Model.stableHomotopy_card (M : SourceHF2Model) (d : ℤ) :
    Nat.card (Prespectrum.StableHomotopy M.spectrum d) = if d = 0 then 2 else 1 := by
  by_cases hd : d = 0
  · subst d
    simpa using (Nat.card_congr M.pi0).trans (Nat.card_zmod 2)
  · letI := M.vanishes d hd
    simp [hd]

/-- Every actual integer shift has finite stable groups in all degrees. -/
theorem SourceHF2Model.shiftStableHomotopy_finite (M : SourceHF2Model) (s d : ℤ) :
    Finite (Prespectrum.StableHomotopy (M.shiftSpectrum s) d) := by
  letI := M.stableHomotopy_finite (d-s)
  exact Finite.of_equiv _ (M.shiftStableHomotopyEquiv s d).symm

/-- The actual shift by s vanishes in every degree different from s. -/
theorem SourceHF2Model.shiftStableHomotopy_vanishes (M : SourceHF2Model) (s d : ℤ)
    (h : d ≠ s) : Subsingleton (Prespectrum.StableHomotopy (M.shiftSpectrum s) d) := by
  letI := M.vanishes (d-s) (by omega)
  exact (M.shiftStableHomotopyEquiv s d).injective.subsingleton

theorem SourceHF2Model.shiftStableHomotopy_card (M : SourceHF2Model) (s d : ℤ) :
    Nat.card (Prespectrum.StableHomotopy (M.shiftSpectrum s) d) = if d = s then 2 else 1 := by
  rw [Nat.card_congr (M.shiftStableHomotopyEquiv s d),M.stableHomotopy_card]
  simp only [sub_eq_zero]

theorem sourceHF2_stableHomotopy_finite (d : ℤ) :
    Finite (Prespectrum.StableHomotopy sourceHF2.spectrum d) :=
  sourceHF2.stableHomotopy_finite d

theorem sourceHF2Shift_eq (s : ℤ) :
    sourceHF2Shift s = sourceLocalization.obj (sourceHF2.shiftSpectrum s) := rfl

/-- These are the actual groups of the existing localized source shift. -/
theorem sourceHF2Shift_stableHomotopy_finite (s d : ℤ) :
    Finite ((sourceStableHomotopyFunctor d).obj (sourceHF2Shift s)) :=
  sourceHF2.shiftStableHomotopy_finite s d

theorem sourceHF2Shift_stableHomotopy_vanishes (s d : ℤ) (h : d ≠ s) :
    Subsingleton ((sourceStableHomotopyFunctor d).obj (sourceHF2Shift s)) :=
  sourceHF2.shiftStableHomotopy_vanishes s d h

theorem sourceHF2Shift_stableHomotopy_card (s d : ℤ) :
    Nat.card ((sourceStableHomotopyFunctor d).obj (sourceHF2Shift s)) =
      if d = s then 2 else 1 :=
  sourceHF2.shiftStableHomotopy_card s d

end KIP126.StableHomotopy.Implementation
