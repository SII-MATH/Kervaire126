module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Proofs
public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.AdjoinPoint.Data
public import KIP126.Def.Topology.HomotopyLifting.Cube.Boundary.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory KIP126.Topology.HomotopyLifting

/-- The whole original cube boundary, including both endpoints of
every coordinate, included in the original parameter tensor. -/
noncomputable def spaceSmashCubeBoundaryMap (n : ℕ) (X : Prespectrum.{0}) :
    spaceSmash (BasedSpace.adjoinPoint (cubeBoundaryObject n)) X ⟶
      spaceSmash (BasedSpace.adjoinPoint (cubeObject n)) X :=
  spaceSmashMap (BasedSpace.adjoinPointMap (cubeBoundaryInclusion n)) (𝟙 X)

end KIP126.StableHomotopy.Implementation.Prespectrum
