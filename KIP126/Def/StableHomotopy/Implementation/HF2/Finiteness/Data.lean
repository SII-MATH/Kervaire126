module

public import KIP126.Def.StableHomotopy.Implementation.Completion
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.SourceShift.Homotopy.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation
open CategoryTheory

/-- The actual integer shift of the source coefficient prespectrum. -/
noncomputable def SourceHF2Model.shiftSpectrum (M : SourceHF2Model) (s : ℤ) : Prespectrum.{0} :=
  if 0 ≤ s then (Prespectrum.suspension^[s.toNat]) M.spectrum
  else (Prespectrum.desuspension^[(-s).toNat]) M.spectrum

/-- The actual cubical stable quotient of a coefficient shift has the
corresponding shifted degree in the original coefficient model. -/
noncomputable def SourceHF2Model.shiftStableHomotopyEquiv (M : SourceHF2Model) (s d : ℤ) :
    Prespectrum.StableHomotopy (M.shiftSpectrum s) d ≃
      Prespectrum.StableHomotopy M.spectrum (d-s) := by
  by_cases hs : 0 ≤ s
  · rw [SourceHF2Model.shiftSpectrum,if_pos hs]
    exact (Prespectrum.stableHomotopyIterateSuspensionEquiv M.spectrum s.toNat d).trans
      (Equiv.cast (congrArg (Prespectrum.StableHomotopy M.spectrum) (by
        rw [Int.toNat_of_nonneg hs])))
  · rw [SourceHF2Model.shiftSpectrum,if_neg hs]
    exact (Prespectrum.stableHomotopyIterateDesuspensionEquiv M.spectrum (-s).toNat d).trans
      (Equiv.cast (congrArg (Prespectrum.StableHomotopy M.spectrum) (by
        rw [Int.toNat_of_nonneg (by omega : 0 ≤ -s)]
        omega)))

/-- The unique supported degree of an actual coefficient shift has two elements. -/
noncomputable def SourceHF2Model.shiftCoefficientEquiv (M : SourceHF2Model) (s : ℤ) :
    Prespectrum.StableHomotopy (M.shiftSpectrum s) s ≃ ZMod 2 :=
  (M.shiftStableHomotopyEquiv s s).trans
    ((Equiv.cast (congrArg (Prespectrum.StableHomotopy M.spectrum) (sub_self s))).trans M.pi0)

/-- The previously fixed sourceHF2Shift uses exactly the actual shifted
coefficient prespectrum whose cubical groups are computed here. -/
noncomputable def sourceHF2ShiftStableHomotopyEquiv (s d : ℤ) :
    (sourceStableHomotopyFunctor d).obj (sourceHF2Shift s) ≃
      Prespectrum.StableHomotopy sourceHF2.spectrum (d-s) :=
  sourceHF2.shiftStableHomotopyEquiv s d

noncomputable def sourceHF2ShiftCoefficientEquiv (s : ℤ) :
    (sourceStableHomotopyFunctor s).obj (sourceHF2Shift s) ≃ ZMod 2 :=
  sourceHF2.shiftCoefficientEquiv s

end KIP126.StableHomotopy.Implementation
