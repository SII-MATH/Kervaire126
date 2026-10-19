module

public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.Smash.Colimit.Existence.Proofs
public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.Smash.Functor.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.BasedSpace
open CategoryTheory CategoryTheory.Limits
universe v w
set_option backward.isDefEq.respectTransparency false

/-- The original smash cocone has the actual colimit universal
property for a compactly generated based diagram and its colimit. -/
noncomputable def smashRight_mapCocone_isColimit
    {J : Type v} [Category.{w} J] (F : J ⥤ BasedSpace.{0})
    (c : Cocone F) (hc : IsColimit c)
    [∀ j, UCompactlyGeneratedSpace.{0} (F.obj j)] (B : BasedSpace.{0}) :
    IsColimit ((smashRightFunctor B).mapCocone c) :=
  IsColimit.ofExistsUnique (fun s => exists_smash_colimit_desc F c hc B s.pt
    (fun j => s.ι.app j) (fun {i j} f => s.w f))

end KIP126.StableHomotopy.Implementation.BasedSpace
