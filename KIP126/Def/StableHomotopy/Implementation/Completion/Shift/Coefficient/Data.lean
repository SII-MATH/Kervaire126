module

public import KIP126.Def.StableHomotopy.Implementation.Completion
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.SourceShift.Equivalence

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory

set_option backward.isDefEq.respectTransparency false

/-- Actual source suspension increments the specified integer coefficient
shift. At negative degrees the comparison is the proved suspension--
desuspension counit, rather than a new recognition assumption. -/
noncomputable def sourceHF2SuspensionShiftIso (d : ℤ) :
    Prespectrum.sourceSuspensionFunctor.obj (sourceHF2Shift d) ≅ sourceHF2Shift (d + 1) := by
  cases d with
  | ofNat n =>
    change Prespectrum.sourceSuspensionFunctor.obj (sourceHF2Shift (n : ℤ)) ≅
      sourceHF2Shift ((n : ℤ) + 1)
    have hn : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by omega
    rw [hn]
    simp only [sourceHF2Shift, Int.natCast_nonneg, if_true, Int.toNat_natCast]
    exact eqToIso (congrArg sourceLocalization.obj
      (Function.iterate_succ_apply' Prespectrum.suspension n sourceHF2.spectrum).symm)
  | negSucc n =>
    cases n with
    | zero =>
      change sourceLocalization.obj (Prespectrum.suspension
        (Prespectrum.desuspension sourceHF2.spectrum)) ≅ sourceLocalization.obj sourceHF2.spectrum
      exact Prespectrum.sourceSuspensionEquivalence.counitIso.app
        (sourceLocalization.obj sourceHF2.spectrum)
    | succ n =>
      have hn : Int.negSucc (n + 1) + 1 = Int.negSucc n := by omega
      rw [hn]
      simp only [sourceHF2Shift, Int.negSucc_not_nonneg, if_false, Int.neg_negSucc,
        Int.toNat_natCast]
      change sourceLocalization.obj
        (Prespectrum.suspension ((Prespectrum.desuspension^[n + 2]) sourceHF2.spectrum)) ≅
          sourceLocalization.obj ((Prespectrum.desuspension^[n + 1]) sourceHF2.spectrum)
      have h : sourceLocalization.obj
          (Prespectrum.suspension (Prespectrum.desuspension
            ((Prespectrum.desuspension^[n + 1]) sourceHF2.spectrum))) ≅
          sourceLocalization.obj ((Prespectrum.desuspension^[n + 1]) sourceHF2.spectrum) :=
        Prespectrum.sourceSuspensionEquivalence.counitIso.app
          (sourceLocalization.obj ((Prespectrum.desuspension^[n + 1]) sourceHF2.spectrum))
      simpa only [Function.iterate_succ_apply'] using
        h

/-- Actual source desuspension decrements the specified integer coefficient
shift, by the inverse comparison and the proved equivalence unit. -/
noncomputable def sourceHF2DesuspensionShiftIso (d : ℤ) :
    Prespectrum.sourceDesuspensionFunctor.obj (sourceHF2Shift d) ≅ sourceHF2Shift (d - 1) :=
  (Prespectrum.sourceSuspensionEquivalence.unitIso.app (sourceHF2Shift (d - 1)) ≪≫
    Prespectrum.sourceDesuspensionFunctor.mapIso
      (sourceHF2SuspensionShiftIso (d - 1) ≪≫ eqToIso (congrArg sourceHF2Shift (by omega)))).symm

end KIP126.StableHomotopy.Implementation
