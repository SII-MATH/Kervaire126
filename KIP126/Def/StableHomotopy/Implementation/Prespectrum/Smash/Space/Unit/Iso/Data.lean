module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Unit.Inverse.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory

/-- The actual zero-sphere smash comparison is a strict isomorphism on
compactly generated original levels, with the specified point-set section. -/
noncomputable def spaceSmashUnitIso (X : Prespectrum.{0})
    [∀ n, UCompactlyGeneratedSpace.{0} (X.level n)] :
    spaceSmash BasedSpace.zeroSphere X ≅ X where
  hom := spaceSmashUnit X
  inv := spaceSmashUnitInverse X
  hom_inv_id := spaceSmashUnit_inverse X
  inv_hom_id := spaceSmashUnitInverse_unit X

end KIP126.StableHomotopy.Implementation.Prespectrum
