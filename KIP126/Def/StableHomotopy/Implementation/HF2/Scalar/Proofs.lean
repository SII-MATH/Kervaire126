module

public import KIP126.Def.StableHomotopy.Implementation.HF2.Scalar.Source.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Completion
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.SourceShift.Integer.Additive.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation
open CategoryTheory
open Prespectrum

/-- Characteristic two for the fixed source coefficient spectrum, using
its explicit original Dold--Kan model. -/
theorem sourceHF2_two_id :
    (2 : ℕ) • 𝟙 (sourceLocalization.obj sourceHF2.spectrum) = 0 :=
  HF2Scalar.hf2RealizationPrespectrum_two_id

/-- Every specified integer shift of the fixed coefficient also has
characteristic two as an actual source object. -/
theorem sourceHF2Shift_two_id (d : ℤ) : (2 : ℕ) • 𝟙 (sourceHF2Shift d) = 0 := by
  have h := congrArg (sourceIntegerShiftFunctor d).map sourceHF2_two_id
  simp only [Functor.map_nsmul,CategoryTheory.Functor.map_id,Functor.map_zero] at h
  rw [sourceIntegerShiftFunctor_obj] at h
  exact h

end KIP126.StableHomotopy.Implementation
