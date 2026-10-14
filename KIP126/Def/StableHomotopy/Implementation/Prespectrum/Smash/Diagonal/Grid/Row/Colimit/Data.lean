module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Diagonal.Grid.Row.Colimit.Representative.Proofs
public import Mathlib.CategoryTheory.Limits.Types.Colimits

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Limits
set_option backward.isDefEq.respectTransparency false

/-- The inclusion of the original vertical stable quotient into the
actual two-index quotient. -/
noncomputable def diagonalGridRowInclusion (X Y : Prespectrum.{0}) (d : ℤ) (n : ℕ) :
    StableHomotopy (spaceSmash (X.level n) Y) (d+n) → DiagonalGridStable X Y d :=
  Quot.lift (fun a => Quot.mk _ (diagonalGridClassOfRowRepresentative X Y d n a))
    (fun _ _ h => diagonalGridClassOfRowRepresentative_relation X Y d n h)

end KIP126.StableHomotopy.Implementation.Prespectrum
