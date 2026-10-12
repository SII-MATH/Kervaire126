module

public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.Suspension.Cell.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.BasedSpace

open CategoryTheory KIP126.Topology.HomotopyLifting

universe u

/-- The actual attaching map on the full boundary of the suspended cube,
glued from its original side map and its two constant end faces. -/
noncomputable def suspensionCellBoundary (n : ℕ) (A : BasedSpace.{u})
    (a : cubeBoundaryObject n ⟶ A.space) :
    cubeBoundaryObject (n+1) ⟶ A.suspension.space :=
  (cubeBoundaryProduct_isPushout n).desc (suspensionCellEnds n A)
    (suspensionCellSide n A a) (suspensionCell_boundary_comm n A a)

end KIP126.StableHomotopy.Implementation.BasedSpace
