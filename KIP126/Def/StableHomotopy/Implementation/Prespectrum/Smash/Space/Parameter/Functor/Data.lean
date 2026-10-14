module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory

/-- The actual fixed-spectrum smash as a functor of its based-space
parameter, with the original spectrum bonds unchanged. -/
noncomputable def spaceSmashParameterFunctor (X : Prespectrum.{0}) :
    BasedSpace.{0} ⥤ Prespectrum.{0} where
  obj A := spaceSmash A X
  map a := spaceSmashMap a (𝟙 X)
  map_id A := spaceSmashMap_id A X
  map_comp a b := by
    simpa only [Category.id_comp] using spaceSmashMap_comp a b (𝟙 X) (𝟙 X)

end KIP126.StableHomotopy.Implementation.Prespectrum
