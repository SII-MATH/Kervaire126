module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Parameter.Product.Naturality.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Parameter.Product.Iso.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
set_option backward.isDefEq.respectTransparency false

/-- Unpairing compact Hausdorff parameters retains both original
parameter maps and the original spectrum map. -/
@[reassoc] theorem spaceSmashParameterProductInverse_natural_parameters
    {S T S' T' : TopCat.{0}}
    [CompactSpace S] [T2Space S] [CompactSpace T] [T2Space T]
    [CompactSpace S'] [T2Space S'] [CompactSpace T'] [T2Space T']
    (a : S ⟶ S') (b : T ⟶ T') {X Y : Prespectrum.{0}} (f : X ⟶ Y) :
    spaceSmashMap (BasedSpace.adjoinPointMap (TopCat.ofHom (a.hom.prodMap b.hom))) f ≫
        (spaceSmashParameterProductIso S' T' Y).inv =
      (spaceSmashParameterProductIso S T X).inv ≫
        spaceSmashMap (BasedSpace.adjoinPointMap a)
          (spaceSmashMap (BasedSpace.adjoinPointMap b) f) := by
  apply (cancel_epi (spaceSmashParameterProductIso S T X).hom).mp
  rw [← Category.assoc]
  change (spaceSmashParameterProduct S T X ≫ _) ≫ _ = _
  rw [← spaceSmashParameterProduct_natural_parameters, Category.assoc]
  change _ ≫ (spaceSmashParameterProductIso S' T' Y).hom ≫
    (spaceSmashParameterProductIso S' T' Y).inv = _
  simp only [Iso.hom_inv_id,Category.comp_id,Iso.hom_inv_id_assoc]

end KIP126.StableHomotopy.Implementation.Prespectrum
