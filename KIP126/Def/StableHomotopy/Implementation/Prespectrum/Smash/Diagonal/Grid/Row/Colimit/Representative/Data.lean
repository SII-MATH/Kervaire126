module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Diagonal.Grid.Stable.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Diagonal.Grid.Row.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
set_option backward.isDefEq.respectTransparency false

/-- An original vertical representative determines its actual two-index
homotopy class. -/
def diagonalGridClassOfRowRepresentative (X Y : Prespectrum.{0}) (d : ℤ) (n : ℕ)
    (a : Representative (spaceSmash (X.level n) Y) (d+n)) :
    DiagonalGridClass X Y d where
  left := n
  right := a.stage
  dimension := a.dimension
  degree := a.degree
  homotopy := ⟦a.loop⟧

/-- A grid homotopy class has an actual stable class in its retained row. -/
noncomputable def DiagonalGridClass.rowClass {X Y : Prespectrum.{0}} {d : ℤ}
    (a : DiagonalGridClass X Y d) :
    StableHomotopy (spaceSmash (X.level a.left) Y) (d+a.left) :=
  Quotient.lift (fun p => Quot.mk _
    ({ stage := a.right, dimension := a.dimension, degree := a.degree, loop := p } :
      Representative (spaceSmash (X.level a.left) Y) (d+a.left)))
    (fun p q h => Quot.sound (StableRelation.homotopy
      { stage := a.right, dimension := a.dimension, degree := a.degree, loop := p } q h))
    a.homotopy

end KIP126.StableHomotopy.Implementation.Prespectrum
