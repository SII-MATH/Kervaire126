module

public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.Smash.LeftFunctor.Data
public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.Smash.Colimit.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.BasedSpace
open CategoryTheory CategoryTheory.Limits
universe v w

/-- The fixed-left smash preserves the original compactly generated
based colimit via its actual natural exchange isomorphism. -/
noncomputable def smashLeft_mapCocone_isColimit
    (A : BasedSpace.{0}) {J : Type v} [Category.{w} J] (F : J ⥤ BasedSpace.{0})
    (c : Cocone F) (hc : IsColimit c)
    [∀ j, UCompactlyGeneratedSpace.{0} (F.obj j)] :
    IsColimit ((smashLeftFunctor A).mapCocone c) := by
  letI : HasColimit F := ⟨⟨c,hc⟩⟩
  letI : PreservesColimit F (smashLeftFunctor A) :=
    preservesColimit_of_natIso F (smashLeftRightIso A).symm
  exact isColimitOfPreserves (smashLeftFunctor A) hc

end KIP126.StableHomotopy.Implementation.BasedSpace
