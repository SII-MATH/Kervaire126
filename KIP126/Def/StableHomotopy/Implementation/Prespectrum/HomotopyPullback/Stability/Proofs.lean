module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyPullback.Lifting.Fiber.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Detection.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

universe u

/-- The actual homotopy-pullback projection preserves the homotopy fiber,
so it is a stable equivalence exactly when the original map is. -/
theorem homotopyPullbackSnd_stableEquivalence_iff {X Y Z : Prespectrum.{u}}
    (f : X ⟶ Y) (g : Z ⟶ Y) :
    stableEquivalences (homotopyPullbackSnd f g) ↔ stableEquivalences f := by
  rw [stableEquivalence_iff_source_fiber_isZero,
    stableEquivalence_iff_source_fiber_isZero]
  exact (sourceHomotopyPullbackFiberIso f g).isZero_iff

/-- Base change along any actual map preserves stable equivalences for
the constructed path homotopy pullback. -/
theorem homotopyPullbackSnd_stableEquivalence {X Y Z : Prespectrum.{u}}
    (f : X ⟶ Y) (g : Z ⟶ Y) (hf : stableEquivalences f) :
    stableEquivalences (homotopyPullbackSnd f g) :=
  (homotopyPullbackSnd_stableEquivalence_iff f g).mpr hf

end KIP126.StableHomotopy.Implementation.Prespectrum
