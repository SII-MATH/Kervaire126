module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Colimit.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Limits

/-- The actual fixed-space smash functor retains each original
colimit of spectra with compactly generated levels. -/
instance spaceSmashFunctor_preservesColimit
    (A : BasedSpace.{0}) {J : Type} [Category.{0} J] (F : J ⥤ Prespectrum.{0})
    [∀ j n, UCompactlyGeneratedSpace.{0} ((F.obj j).level n)] :
    PreservesColimit F (spaceSmashFunctor A) :=
  preservesColimit_of_preserves_colimit_cocone (colimit.isColimit F)
    (spaceSmash_mapCocone_isColimit A F (colimit.cocone F) (colimit.isColimit F))

end KIP126.StableHomotopy.Implementation.Prespectrum
