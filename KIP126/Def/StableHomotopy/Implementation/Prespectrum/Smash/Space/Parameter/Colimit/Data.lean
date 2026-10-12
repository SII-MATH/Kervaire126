module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Parameter.Functor.Data
public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.Smash.Colimit.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Colimit.Evaluation.Reflection.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Limits
universe v w
set_option backward.isDefEq.respectTransparency false

/-- The actual space-smash parameter cocone is colimiting. This is a
strict point-set statement, with no stability or flatness hypothesis. -/
noncomputable def spaceSmashParameter_mapCocone_isColimit
    {J : Type v} [Category.{w} J] (F : J ⥤ BasedSpace.{0})
    (c : Cocone F) (hc : IsColimit c)
    [∀ j, UCompactlyGeneratedSpace.{0} (F.obj j)] (X : Prespectrum.{0}) :
    IsColimit ((spaceSmashParameterFunctor X).mapCocone c) :=
  isColimit_of_evaluation _ (fun n =>
    BasedSpace.smashRight_mapCocone_isColimit F c hc (X.level n))

end KIP126.StableHomotopy.Implementation.Prespectrum
