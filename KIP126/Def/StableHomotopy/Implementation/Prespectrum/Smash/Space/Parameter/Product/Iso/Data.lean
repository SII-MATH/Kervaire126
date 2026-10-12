module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Parameter.Product.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

/-- Two actual compact Hausdorff parameter tensors are strictly
isomorphic to tensoring by their original product, without changing any
topology or requiring compact generation of the original spectrum. -/
noncomputable def spaceSmashParameterProductIso (S T : TopCat.{0})
    [CompactSpace S] [T2Space S] [CompactSpace T] [T2Space T] (X : Prespectrum.{0}) :
    spaceSmash (BasedSpace.adjoinPoint S) (spaceSmash (BasedSpace.adjoinPoint T) X) ≅
      spaceSmash (BasedSpace.adjoinPoint (TopCat.of (S × T))) X where
  hom := spaceSmashParameterProduct S T X
  inv := spaceSmashParameterProductInverse S T X
  hom_inv_id := spaceSmashParameterProduct_inverse S T X
  inv_hom_id := spaceSmashParameterProductInverse_product S T X

end KIP126.StableHomotopy.Implementation.Prespectrum
