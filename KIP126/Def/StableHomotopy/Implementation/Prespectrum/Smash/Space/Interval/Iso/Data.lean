module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Interval.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory
open scoped unitInterval

/-- The interval tensor with the actual disjoint basepoint is strictly
isomorphic to the original reduced cylinder of the identity. All spaces
retain their original topology. -/
noncomputable def spaceSmashIntervalIso (X : Prespectrum.{0})
    [∀ n, UCompactlyGeneratedSpace.{0} (X.level n)] :
    spaceSmash (BasedSpace.adjoinPoint (TopCat.of I)) X ≅ mappingCylinder (𝟙 X) where
  hom := spaceSmashIntervalComparison X
  inv := spaceSmashIntervalInverse X
  hom_inv_id := spaceSmashIntervalComparison_inverse X
  inv_hom_id := spaceSmashIntervalInverse_comparison X

end KIP126.StableHomotopy.Implementation.Prespectrum
