module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Interval.Boundary.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits _root_.Topology
open KIP126.Topology.HomotopyLifting

/-- Smashing with the two actual interval endpoints with a disjoint basepoint
is strictly the binary coproduct, with zero on the left and one on the right. -/
noncomputable def spaceSmashIntervalBoundaryIso (X : Prespectrum.{0})
    [∀ n, UCompactlyGeneratedSpace.{0} (X.level n)] :
    spaceSmash (BasedSpace.adjoinPoint intervalBoundaryObject) X ≅ X ⨿ X where
  hom := spaceSmashIntervalBoundaryComparison X
  inv := spaceSmashIntervalBoundaryInverse X
  hom_inv_id := spaceSmashIntervalBoundaryComparison_inverse X
  inv_hom_id := spaceSmashIntervalBoundaryInverse_comparison X

end KIP126.StableHomotopy.Implementation.Prespectrum
