module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Diagonal.Grid.Loop.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

/-- The horizontal grid transition on original stable representatives.
The row degree increases by one, while the vertical spectrum stage stays fixed. -/
noncomputable def diagonalGridRowRepresentative (X Y : Prespectrum.{0}) (d : ℤ) (n : ℕ)
    (a : Representative (spaceSmash (X.level n) Y) (d+n)) :
    Representative (spaceSmash (X.level (n+1)) Y) (d+(n+1)) where
  stage := a.stage
  dimension := a.dimension+1
  degree := by have := a.degree; omega
  loop := diagonalGridLoopHorizontal X Y n a.stage a.dimension a.loop

end KIP126.StableHomotopy.Implementation.Prespectrum
