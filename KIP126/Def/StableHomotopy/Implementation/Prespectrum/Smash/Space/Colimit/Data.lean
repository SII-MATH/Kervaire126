module

public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.Smash.LeftFunctor.Colimit.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Functor.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Colimit.Evaluation.Reflection.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false

/-- Actual fixed-space smash preserves a strict diagram colimit
whenever each original spectrum level in the diagram is compactly
generated. No condition is placed on the fixed based space. -/
noncomputable def spaceSmash_mapCocone_isColimit
    (A : BasedSpace.{0}) {J : Type} [Category.{0} J] (F : J ⥤ Prespectrum.{0})
    (c : Cocone F) (hc : IsColimit c)
    [∀ j n, UCompactlyGeneratedSpace.{0} ((F.obj j).level n)] :
    IsColimit ((spaceSmashFunctor A).mapCocone c) := by
  apply isColimit_of_evaluation
  intro n
  letI (j : J) : UCompactlyGeneratedSpace.{0} ((F ⋙ evaluationFunctor n).obj j) :=
    inferInstanceAs (UCompactlyGeneratedSpace.{0} ((F.obj j).level n))
  exact BasedSpace.smashLeft_mapCocone_isColimit A (F ⋙ evaluationFunctor n)
    ((evaluationFunctor n).mapCocone c) (isColimitOfPreserves (evaluationFunctor n) hc)

end KIP126.StableHomotopy.Implementation.Prespectrum
