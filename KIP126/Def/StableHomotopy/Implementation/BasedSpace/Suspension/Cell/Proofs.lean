module

public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.Suspension.Cell.Data
public import KIP126.Def.Topology.Pushout.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.BasedSpace

open CategoryTheory CategoryTheory.Limits KIP126.Topology.HomotopyLifting
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- The prescribed end faces and side boundary agree on their actual
intersection, including the empty zero-dimensional boundary. -/
theorem suspensionCell_boundary_comm (n : ℕ) (A : BasedSpace.{u})
    (a : cubeBoundaryObject n ⟶ A.space) :
    cubeBoundaryProductTop n ≫ suspensionCellEnds n A =
      cubeBoundaryProductLeft n ≫ suspensionCellSide n A a := by
  ext x
  exact (suspensionProjection_collapsed A _ (Or.inr x.1.property)).symm

end KIP126.StableHomotopy.Implementation.BasedSpace
