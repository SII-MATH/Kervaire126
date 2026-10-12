module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Cofibration.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u

/-- Strict isomorphisms have the actual cubical left lifting property. -/
theorem isCubicalCofibration_of_isIso {X Y : Prespectrum.{u}}
    (i : X ⟶ Y) [IsIso i] : IsCubicalCofibration i := by
  intro E B p hp
  infer_instance

end KIP126.StableHomotopy.Implementation.Prespectrum
