module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Parameter.Product.Iso.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Iso.Data
public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.AdjoinPoint.Cube.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory KIP126.Topology.HomotopyLifting
open scoped unitInterval

/-- The original successor cube tensor is strictly the interval tensor
of the preceding original cube tensor, by actual coordinate and smash
isomorphisms. -/
noncomputable def spaceSmashCubeSuccIso (n : ℕ) (X : Prespectrum.{0}) :
    spaceSmash (BasedSpace.adjoinPoint (cubeObject (n+1))) X ≅
      spaceSmash (BasedSpace.adjoinPoint (TopCat.of I))
        (spaceSmash (BasedSpace.adjoinPoint (cubeObject n)) X) :=
  spaceSmashIso (BasedSpace.adjoinPointCubeSuccIso n) (Iso.refl X) ≪≫
    (spaceSmashParameterProductIso (TopCat.of I) (cubeObject n) X).symm

end KIP126.StableHomotopy.Implementation.Prespectrum
