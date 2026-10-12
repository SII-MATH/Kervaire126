module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open scoped unitInterval

/-- The horizontal bond of the actual two-index smash grid. The interval
acts on the first spectrum and the second point is retained. -/
noncomputable def diagonalGridBondLeft (X Y : Prespectrum.{0}) (n k : ℕ) :
    C(((X.level n).smash (Y.level k)) × I, (X.level (n+1)).smash (Y.level k)) :=
  BasedSpace.smashFamily (X.bond n) ContinuousMap.fst (X.bond_point n) (fun _ => rfl)

end KIP126.StableHomotopy.Implementation.Prespectrum
