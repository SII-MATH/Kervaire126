module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory

/-- The actual fixed-space smash functor before localization. -/
noncomputable def spaceSmashFunctor (A : BasedSpace.{0}) : Prespectrum.{0} ⥤ Prespectrum.{0} where
  obj := spaceSmash A
  map := spaceSmashMap (𝟙 A)
  map_id X := spaceSmashMap_id A X
  map_comp f g := by
    simpa only [Category.id_comp] using spaceSmashMap_comp (𝟙 A) (𝟙 A) f g

end KIP126.StableHomotopy.Implementation.Prespectrum
