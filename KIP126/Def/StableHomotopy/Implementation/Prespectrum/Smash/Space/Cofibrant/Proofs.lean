module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Unit.Iso.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Stability.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Cofibrant.Topology.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Cofibrant.Iso.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Cofibration.Suspension.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory

/-- Each original fixed sphere smash preserves actual cubical cofibrancy,
using strict unit and suspension comparisons. -/
theorem IsCubicallyCofibrant.spaceSmash_sphere {X : Prespectrum.{0}}
    (hX : IsCubicallyCofibrant X) (n : ℕ) :
    IsCubicallyCofibrant (spaceSmash (sphereLevel n) X) := by
  induction n with
  | zero =>
    letI (k : ℕ) := hX.level_uCompactlyGeneratedSpace k
    intro E B p hp
    exact IsCubicallyCofibrant.of_iso hX (spaceSmashUnitIso X).symm p hp
  | succ n ih =>
    letI := (sphereLevel_good n).1
    intro E B p hp
    exact IsCubicallyCofibrant.of_iso
      (IsCubicallyCofibrant.suspension ih)
      (spaceSmashSuspensionIso (sphereLevel n) X).symm p hp

end KIP126.StableHomotopy.Implementation.Prespectrum
