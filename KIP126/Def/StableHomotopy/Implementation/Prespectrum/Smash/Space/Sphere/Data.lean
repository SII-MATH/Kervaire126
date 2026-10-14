module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Stability.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.SourceShift.Homotopy.Data

@[expose] public section
namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
set_option backward.isDefEq.respectTransparency false

/-- Actual smash with the fixed n-sphere shifts the original stable
homotopy groups by n, via the explicit unit and suspension comparisons. -/
noncomputable def stableHomotopySpaceSmashSphereEquiv (X : Prespectrum.{0})
    (n : ℕ) (d : ℤ) :
    StableHomotopy (spaceSmash (sphereLevel n) X) d ≃ StableHomotopy X (d-n) := by
  induction n generalizing d with
  | zero =>
    simp only [Nat.cast_zero,sub_zero]
    exact Equiv.ofBijective (stableHomotopyMap (spaceSmashUnit X) d)
      (spaceSmashUnit_stableEquivalence X d)
  | succ n ih =>
    letI := (sphereLevel_good n).1
    exact (stableHomotopyEquivOfSourceIso
      (sourceLocalization.mapIso (spaceSmashSuspensionIso (sphereLevel n) X)) d).trans
      ((stableHomotopySuspensionEquiv (spaceSmash (sphereLevel n) X) d).trans
        ((ih (d-1)).trans (Equiv.cast (congrArg (StableHomotopy X) (by push_cast; omega)))))

end KIP126.StableHomotopy.Implementation.Prespectrum
