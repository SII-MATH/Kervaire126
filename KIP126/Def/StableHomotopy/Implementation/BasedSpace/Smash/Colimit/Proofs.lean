module

public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.Smash.Colimit.Data
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.BasedSpace
open CategoryTheory CategoryTheory.Limits
universe v w

/-- Actual smash preserves each existing colimit of compactly
generated based spaces. The second factor is arbitrary. -/
instance smashRightFunctor_preservesColimit
    {J : Type v} [Category.{w} J] (F : J ⥤ BasedSpace.{0})
    [HasColimit F] [∀ j, UCompactlyGeneratedSpace.{0} (F.obj j)]
    (B : BasedSpace.{0}) : PreservesColimit F (smashRightFunctor B) :=
  preservesColimit_of_preserves_colimit_cocone (colimit.isColimit F)
    (smashRight_mapCocone_isColimit F (colimit.cocone F) (colimit.isColimit F) B)

end KIP126.StableHomotopy.Implementation.BasedSpace
