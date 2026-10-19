module

public import KIP126.Def.StableHomotopy.Implementation.Completion.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyFunctor.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory

/-- Reflection of an already local point-set object preserves its actual
cubical stable homotopy groups, not merely abstract source morphisms. -/
theorem CompletionModel.unit_stableEquivalence_of_local (M : CompletionModel)
    (X : Prespectrum.{0}) (hX : X.IsHF2Local) :
    Prespectrum.stableEquivalences (M.unit.app X) :=
  (Prespectrum.stableEquivalence_iff_source_isIso _).mpr (M.unit_isIso_of_local X hX)

/-- Each of the specified integer source coefficient shifts is local by
the exact testing definition of mod-two cohomology equivalence. -/
theorem sourceHF2Shift_isLocal (d : ℤ) :
    (if 0 ≤ d then (Prespectrum.suspension^[d.toNat]) sourceHF2.spectrum
      else (Prespectrum.desuspension^[(-d).toNat]) sourceHF2.spectrum).IsHF2Local :=
  fun _ hf => hf d

/-- In particular the original source coefficient spectrum is local. -/
theorem sourceHF2_isLocal : sourceHF2.spectrum.IsHF2Local := by
  intro A B f hf
  simpa [sourceHF2Shift] using hf 0

/-- The actual unit on the source coefficient spectrum is a stable
weak equivalence for every supplied reflection with its universal property. -/
theorem CompletionModel.hf2_unit_stableEquivalence (M : CompletionModel) :
    Prespectrum.stableEquivalences (M.unit.app sourceHF2.spectrum) :=
  M.unit_stableEquivalence_of_local _ sourceHF2_isLocal

/-- Source completion preserves the actual vanishing groups of HF₂. -/
theorem CompletionModel.hf2_stableHomotopy_subsingleton (M : CompletionModel)
    (d : ℤ) (hd : d ≠ 0) :
    Subsingleton (Prespectrum.StableHomotopy (M.replacement.obj sourceHF2.spectrum) d) := by
  letI : Subsingleton (Prespectrum.StableHomotopy
    ((𝟭 Prespectrum.{0}).obj sourceHF2.spectrum) d) := sourceHF2.vanishes d hd
  exact (M.hf2_unit_stableEquivalence d).surjective.subsingleton

end KIP126.StableHomotopy.Implementation
