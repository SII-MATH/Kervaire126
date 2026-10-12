module

public import KIP126.Def.StableHomotopy.Implementation.Completion.Shift.Integer.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory KIP126.Foundation

set_option backward.isDefEq.respectTransparency false

namespace CompletedSpectrum

@[simp] theorem integerShiftFunctor_one : integerShiftFunctor 1 = suspensionFunctor := rfl

@[simp] theorem integerShiftFunctor_neg_one : integerShiftFunctor (-1) = desuspensionFunctor := rfl

theorem suspensionIterate_spectrum (n : ℕ) (X : CompletedSpectrum) :
    ((functorIterate suspensionFunctor n).obj X).spectrum =
      (Prespectrum.suspension^[n]) X.spectrum := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ((functorIterate suspensionFunctor n).obj X).spectrum.suspension = _
    rw [ih, Function.iterate_succ_apply']

theorem desuspensionIterate_spectrum (n : ℕ) (X : CompletedSpectrum) :
    ((functorIterate desuspensionFunctor n).obj X).spectrum =
      (Prespectrum.desuspension^[n]) X.spectrum := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ((functorIterate desuspensionFunctor n).obj X).spectrum.desuspension = _
    rw [ih, Function.iterate_succ_apply']

/-- Every signed local iterate is represented by exactly the specified
point-set suspension or padded desuspension iterate. -/
theorem integerShiftFunctor_obj_spectrum (d : ℤ) (X : CompletedSpectrum) :
    ((integerShiftFunctor d).obj X).spectrum =
      if 0 ≤ d then (Prespectrum.suspension^[d.toNat]) X.spectrum
      else (Prespectrum.desuspension^[(-d).toNat]) X.spectrum := by
  cases d with
  | ofNat n =>
    simpa only [integerShiftFunctor, Int.ofNat_eq_natCast, Int.natCast_nonneg,
      if_true, Int.toNat_natCast] using suspensionIterate_spectrum n X
  | negSucc n =>
    simpa only [integerShiftFunctor, Int.negSucc_not_nonneg, if_false,
      Int.neg_negSucc, Int.toNat_natCast] using desuspensionIterate_spectrum (n + 1) X

end CompletedSpectrum

/-- HF₂ locality is preserved by every exact point-set integer shift. -/
theorem Prespectrum.IsHF2Local.integerShift {X : Prespectrum.{0}} (hX : X.IsHF2Local) (d : ℤ) :
    (if 0 ≤ d then (Prespectrum.suspension^[d.toNat]) X
      else (Prespectrum.desuspension^[(-d).toNat]) X).IsHF2Local := by
  let Y : CompletedSpectrum := ⟨X, hX⟩
  have h : ((CompletedSpectrum.integerShiftFunctor d).obj Y).spectrum.IsHF2Local :=
    ((CompletedSpectrum.integerShiftFunctor d).obj Y).isLocal
  rw [CompletedSpectrum.integerShiftFunctor_obj_spectrum] at h
  intro A B f hf
  exact h f hf

/-- The original fixed coefficient-shift object is exactly the value of the
signed source iterate family on the original source HF₂ spectrum. -/
theorem sourceHF2Shift_eq_integerShiftFunctor (d : ℤ) :
    sourceHF2Shift d = (Prespectrum.sourceIntegerShiftFunctor d).obj
      (sourceLocalization.obj sourceHF2.spectrum) :=
  (Prespectrum.sourceIntegerShiftFunctor_obj d sourceHF2.spectrum).symm

end KIP126.StableHomotopy.Implementation
