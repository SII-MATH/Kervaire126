module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Parameter.Product.Level.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

set_option backward.isDefEq.respectTransparency false

@[simp] theorem parameterSmashProductComparison_apply (S T : TopCat.{0}) (s : S) (t : T) :
    (parameterSmashProductComparison S T).map
      (BasedSpace.smashPoint _ _ (.inl s) (.inl t)) = .inl (s, t) := rfl

@[simp] theorem parameterSmashProductInverse_apply (S T : TopCat.{0})
    [CompactSpace S] [T2Space S] [CompactSpace T] [T2Space T] (s : S) (t : T) :
    (parameterSmashProductInverse S T).map (.inl (s, t)) =
      BasedSpace.smashPoint (BasedSpace.adjoinPoint S) (BasedSpace.adjoinPoint T)
        (.inl s) (.inl t) := rfl

/-- The representative formula includes the two collapsed parameter
basepoints and is independent of the target based space. -/
theorem spaceSmashParameterProductLevel_apply_all (S T : TopCat.{0}) (A : BasedSpace.{0})
    (s : BasedSpace.adjoinPoint S) (t : BasedSpace.adjoinPoint T) (x : A) :
    (spaceSmashParameterProductLevel S T A).map
      (BasedSpace.smashPoint _ _ s (BasedSpace.smashPoint _ _ t x)) =
      BasedSpace.smashPoint _ _
        ((parameterSmashProductComparison S T).map (BasedSpace.smashPoint _ _ s t)) x := by
  change (BasedSpace.smashMap (parameterSmashProductComparison S T) (𝟙 A)).map
    ((BasedSpace.smashAssocInverse _ _ _).map
      (BasedSpace.smashPoint _ _ s (BasedSpace.smashPoint _ _ t x))) = _
  rw [BasedSpace.smashAssocInverse_apply, BasedSpace.smashMap_apply]
  rfl

@[simp] theorem spaceSmashParameterProductLevel_apply (S T : TopCat.{0}) (A : BasedSpace.{0})
    (s : S) (t : T) (x : A) :
    (spaceSmashParameterProductLevel S T A).map
      (BasedSpace.smashPoint _ _ (.inl s) (BasedSpace.smashPoint _ _ (.inl t) x)) =
      BasedSpace.smashPoint (BasedSpace.adjoinPoint (TopCat.of (S × T))) A (.inl (s, t)) x := by
  rw [spaceSmashParameterProductLevel_apply_all, parameterSmashProductComparison_apply]

@[simp] theorem spaceSmashParameterProductInverseLevel_apply (S T : TopCat.{0})
    [CompactSpace S] [T2Space S] [CompactSpace T] [T2Space T] (A : BasedSpace.{0})
    (s : S) (t : T) (x : A) :
    (spaceSmashParameterProductInverseLevel S T A).map
      (BasedSpace.smashPoint _ _ (.inl (s, t)) x) =
      BasedSpace.smashPoint (BasedSpace.adjoinPoint S) ((BasedSpace.adjoinPoint T).smash A)
        (.inl s) (BasedSpace.smashPoint (BasedSpace.adjoinPoint T) A (.inl t) x) := by
  change (BasedSpace.smashAssoc _ _ _).map
    ((BasedSpace.smashMap (parameterSmashProductInverse S T) (𝟙 A)).map
      (BasedSpace.smashPoint _ _ (.inl (s, t)) x)) = _
  rw [BasedSpace.smashMap_apply, parameterSmashProductInverse_apply, BasedSpace.smashAssoc_apply]
  rfl

/-- The level maps are inverses on the actual nested quotient. -/
theorem spaceSmashParameterProductLevel_inverse (S T : TopCat.{0})
    [CompactSpace S] [T2Space S] [CompactSpace T] [T2Space T] (A : BasedSpace.{0}) :
    spaceSmashParameterProductLevel S T A ≫ spaceSmashParameterProductInverseLevel S T A = 𝟙 _ := by
  apply BasedSpace.Hom.ext
  apply ContinuousMap.ext
  intro z
  refine Quot.inductionOn z ?_
  rintro ⟨s, z⟩
  refine Quot.inductionOn z ?_
  rintro ⟨t, x⟩
  change (spaceSmashParameterProductInverseLevel S T A).map
    ((spaceSmashParameterProductLevel S T A).map
      (BasedSpace.smashPoint _ _ s (BasedSpace.smashPoint _ _ t x))) =
    BasedSpace.smashPoint _ _ s (BasedSpace.smashPoint _ _ t x)
  cases s with
  | inl s =>
    cases t with
    | inl t => rw [spaceSmashParameterProductLevel_apply, spaceSmashParameterProductInverseLevel_apply]
    | inr t =>
      cases t
      change (spaceSmashParameterProductInverseLevel S T A).map
        ((spaceSmashParameterProductLevel S T A).map
          (BasedSpace.smashPoint _ _ (.inl s)
            (BasedSpace.smashPoint (BasedSpace.adjoinPoint T) A (BasedSpace.adjoinPoint T).point x))) = _
      rw [BasedSpace.smashPoint_base_left, BasedSpace.smashPoint_base_right,
        (spaceSmashParameterProductLevel S T A).point,
        (spaceSmashParameterProductInverseLevel S T A).point]
      change _ = BasedSpace.smashPoint (BasedSpace.adjoinPoint S) ((BasedSpace.adjoinPoint T).smash A) (.inl s)
        (BasedSpace.smashPoint (BasedSpace.adjoinPoint T) A (BasedSpace.adjoinPoint T).point x)
      rw [BasedSpace.smashPoint_base_left, BasedSpace.smashPoint_base_right]
  | inr s =>
    cases s
    change (spaceSmashParameterProductInverseLevel S T A).map
      ((spaceSmashParameterProductLevel S T A).map
        (BasedSpace.smashPoint (BasedSpace.adjoinPoint S) _ (BasedSpace.adjoinPoint S).point
          (BasedSpace.smashPoint _ _ t x))) = _
    rw [BasedSpace.smashPoint_base_left, (spaceSmashParameterProductLevel S T A).point,
      (spaceSmashParameterProductInverseLevel S T A).point]
    change _ = BasedSpace.smashPoint (BasedSpace.adjoinPoint S) _ (BasedSpace.adjoinPoint S).point
      (BasedSpace.smashPoint _ _ t x)
    rw [BasedSpace.smashPoint_base_left]

/-- The inverse comparison also retains every original product parameter. -/
theorem spaceSmashParameterProductInverseLevel_product (S T : TopCat.{0})
    [CompactSpace S] [T2Space S] [CompactSpace T] [T2Space T] (A : BasedSpace.{0}) :
    spaceSmashParameterProductInverseLevel S T A ≫ spaceSmashParameterProductLevel S T A = 𝟙 _ := by
  apply BasedSpace.Hom.ext
  apply ContinuousMap.ext
  intro z
  refine Quot.inductionOn z ?_
  rintro ⟨p, x⟩
  change (spaceSmashParameterProductLevel S T A).map
    ((spaceSmashParameterProductInverseLevel S T A).map (BasedSpace.smashPoint _ _ p x)) =
      BasedSpace.smashPoint _ _ p x
  cases p with
  | inl p => rw [spaceSmashParameterProductInverseLevel_apply, spaceSmashParameterProductLevel_apply]
  | inr p =>
    cases p
    change (spaceSmashParameterProductLevel S T A).map
      ((spaceSmashParameterProductInverseLevel S T A).map
        (BasedSpace.smashPoint (BasedSpace.adjoinPoint (TopCat.of (S × T))) _
          (BasedSpace.adjoinPoint (TopCat.of (S × T))).point x)) = _
    rw [BasedSpace.smashPoint_base_left, (spaceSmashParameterProductInverseLevel S T A).point,
      (spaceSmashParameterProductLevel S T A).point]
    change _ = BasedSpace.smashPoint (BasedSpace.adjoinPoint (TopCat.of (S × T))) A
      (BasedSpace.adjoinPoint (TopCat.of (S × T))).point x
    rw [BasedSpace.smashPoint_base_left]

end KIP126.StableHomotopy.Implementation.Prespectrum
