module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Parameter.Product.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.CompactlyGenerated.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

set_option backward.isDefEq.respectTransparency false

@[simp] theorem spaceSmashParameterProduct_apply (S T : TopCat.{0}) (X : Prespectrum.{0})
    (n : ℕ) (s : S) (t : T) (x : X.level n) :
    (spaceSmashParameterProduct S T X).level n
      (BasedSpace.smashPoint _ _ (.inl s) (BasedSpace.smashPoint _ _ (.inl t) x)) =
      BasedSpace.smashPoint (BasedSpace.adjoinPoint (TopCat.of (S × T))) (X.level n) (.inl (s, t)) x :=
  spaceSmashParameterProductLevel_apply S T (X.level n) s t x

@[simp] theorem spaceSmashParameterProductInverse_apply (S T : TopCat.{0})
    [CompactSpace S] [T2Space S] [CompactSpace T] [T2Space T] (X : Prespectrum.{0})
    (n : ℕ) (s : S) (t : T) (x : X.level n) :
    (spaceSmashParameterProductInverse S T X).level n (BasedSpace.smashPoint _ _ (.inl (s, t)) x) =
      BasedSpace.smashPoint (BasedSpace.adjoinPoint S) ((BasedSpace.adjoinPoint T).smash (X.level n))
        (.inl s) (BasedSpace.smashPoint (BasedSpace.adjoinPoint T) (X.level n) (.inl t) x) :=
  spaceSmashParameterProductInverseLevel_apply S T (X.level n) s t x

theorem spaceSmashParameterProduct_inverse (S T : TopCat.{0})
    [CompactSpace S] [T2Space S] [CompactSpace T] [T2Space T] (X : Prespectrum.{0}) :
    spaceSmashParameterProduct S T X ≫ spaceSmashParameterProductInverse S T X = 𝟙 _ := by
  apply Hom.ext
  funext n
  exact congrArg BasedSpace.Hom.map (spaceSmashParameterProductLevel_inverse S T (X.level n))

theorem spaceSmashParameterProductInverse_product (S T : TopCat.{0})
    [CompactSpace S] [T2Space S] [CompactSpace T] [T2Space T] (X : Prespectrum.{0}) :
    spaceSmashParameterProductInverse S T X ≫ spaceSmashParameterProduct S T X = 𝟙 _ := by
  apply Hom.ext
  funext n
  exact congrArg BasedSpace.Hom.map (spaceSmashParameterProductInverseLevel_product S T (X.level n))

/-- Pairing the actual parameter coordinates is strictly natural in
all spectrum maps, before any stable localization or replacement. -/
@[reassoc] theorem spaceSmashParameterProduct_natural (S T : TopCat.{0})
    {X Y : Prespectrum.{0}} (f : X ⟶ Y) :
    spaceSmashMap (𝟙 (BasedSpace.adjoinPoint S))
        (spaceSmashMap (𝟙 (BasedSpace.adjoinPoint T)) f) ≫ spaceSmashParameterProduct S T Y =
      spaceSmashParameterProduct S T X ≫
        spaceSmashMap (𝟙 (BasedSpace.adjoinPoint (TopCat.of (S × T)))) f := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  refine Quot.inductionOn z ?_
  rintro ⟨s, z⟩
  refine Quot.inductionOn z ?_
  rintro ⟨t, x⟩
  change (spaceSmashParameterProductLevel S T (Y.level n)).map
    ((spaceSmashMap (𝟙 (BasedSpace.adjoinPoint S))
      (spaceSmashMap (𝟙 (BasedSpace.adjoinPoint T)) f)).level n
        (BasedSpace.smashPoint _ _ s (BasedSpace.smashPoint _ _ t x))) = _
  rw [spaceSmashMap_apply, spaceSmashMap_apply]
  change (spaceSmashParameterProductLevel S T (Y.level n)).map
    (BasedSpace.smashPoint (BasedSpace.adjoinPoint S) ((BasedSpace.adjoinPoint T).smash (Y.level n))
      s (BasedSpace.smashPoint (BasedSpace.adjoinPoint T) (Y.level n) t (f.level n x))) = _
  rw [spaceSmashParameterProductLevel_apply_all]
  change _ = (spaceSmashMap (𝟙 (BasedSpace.adjoinPoint (TopCat.of (S × T)))) f).level n
    ((spaceSmashParameterProductLevel S T (X.level n)).map
      (BasedSpace.smashPoint _ _ s (BasedSpace.smashPoint _ _ t x)))
  rw [spaceSmashParameterProductLevel_apply_all, spaceSmashMap_apply]
  rfl

end KIP126.StableHomotopy.Implementation.Prespectrum
