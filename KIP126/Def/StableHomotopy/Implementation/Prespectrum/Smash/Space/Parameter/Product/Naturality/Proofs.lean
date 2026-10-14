module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Parameter.Product.Proofs
public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.AdjoinPoint.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
set_option backward.isDefEq.respectTransparency false

/-- The original product-parameter comparison is natural in both
parameter maps and the spectrum map, including collapsed basepoints. -/
@[reassoc] theorem spaceSmashParameterProduct_natural_parameters
    {S T S' T' : TopCat.{0}} (a : S ⟶ S') (b : T ⟶ T')
    {X Y : Prespectrum.{0}} (f : X ⟶ Y) :
    spaceSmashMap (BasedSpace.adjoinPointMap a)
        (spaceSmashMap (BasedSpace.adjoinPointMap b) f) ≫
          spaceSmashParameterProduct S' T' Y =
      spaceSmashParameterProduct S T X ≫
        spaceSmashMap (BasedSpace.adjoinPointMap (TopCat.ofHom (a.hom.prodMap b.hom))) f := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  refine Quot.inductionOn z ?_
  rintro ⟨s,z⟩
  refine Quot.inductionOn z ?_
  rintro ⟨t,x⟩
  change (spaceSmashParameterProductLevel S' T' (Y.level n)).map
    ((spaceSmashMap (BasedSpace.adjoinPointMap a)
      (spaceSmashMap (BasedSpace.adjoinPointMap b) f)).level n
        (BasedSpace.smashPoint _ _ s (BasedSpace.smashPoint _ _ t x))) = _
  rw [spaceSmashMap_apply,spaceSmashMap_apply]
  change (spaceSmashParameterProductLevel S' T' (Y.level n)).map
    (BasedSpace.smashPoint (BasedSpace.adjoinPoint S') ((BasedSpace.adjoinPoint T').smash (Y.level n))
      ((BasedSpace.adjoinPointMap a).map s)
      (BasedSpace.smashPoint (BasedSpace.adjoinPoint T') (Y.level n)
        ((BasedSpace.adjoinPointMap b).map t) (f.level n x))) = _
  rw [spaceSmashParameterProductLevel_apply_all]
  change _ = (spaceSmashMap
    (BasedSpace.adjoinPointMap (TopCat.ofHom (a.hom.prodMap b.hom))) f).level n
      ((spaceSmashParameterProductLevel S T (X.level n)).map
        (BasedSpace.smashPoint _ _ s (BasedSpace.smashPoint _ _ t x)))
  rw [spaceSmashParameterProductLevel_apply_all,spaceSmashMap_apply]
  cases s <;> cases t <;> rfl

end KIP126.StableHomotopy.Implementation.Prespectrum
