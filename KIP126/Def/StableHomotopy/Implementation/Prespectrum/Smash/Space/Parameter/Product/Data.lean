module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Parameter.Product.Level.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory
open scoped unitInterval

set_option backward.isDefEq.respectTransparency false

/-- Nested actual parameter tensors pair their parameters while
retaining the original spectrum bonds. -/
noncomputable def spaceSmashParameterProduct (S T : TopCat.{0}) (X : Prespectrum.{0}) :
    spaceSmash (BasedSpace.adjoinPoint S) (spaceSmash (BasedSpace.adjoinPoint T) X) ⟶
      spaceSmash (BasedSpace.adjoinPoint (TopCat.of (S × T))) X where
  level n := (spaceSmashParameterProductLevel S T (X.level n)).map
  point n := (spaceSmashParameterProductLevel S T (X.level n)).point
  bond n z r := by
    refine Quot.inductionOn z ?_
    rintro ⟨s, z⟩
    refine Quot.inductionOn z ?_
    rintro ⟨t, x⟩
    change (spaceSmashParameterProductLevel S T (X.level (n+1))).map
      ((spaceSmash (BasedSpace.adjoinPoint S) (spaceSmash (BasedSpace.adjoinPoint T) X)).bond n
        (BasedSpace.smashPoint _ _ s (BasedSpace.smashPoint _ _ t x), r)) = _
    rw [spaceSmash_bond, spaceSmash_bond]
    change (spaceSmashParameterProductLevel S T (X.level (n+1))).map
      (BasedSpace.smashPoint (BasedSpace.adjoinPoint S) ((BasedSpace.adjoinPoint T).smash (X.level (n+1)))
        s (BasedSpace.smashPoint (BasedSpace.adjoinPoint T) (X.level (n+1)) t (X.bond n (x, r)))) = _
    rw [spaceSmashParameterProductLevel_apply_all]
    change _ = (spaceSmash (BasedSpace.adjoinPoint (TopCat.of (S × T))) X).bond n
      ((spaceSmashParameterProductLevel S T (X.level n)).map
        (BasedSpace.smashPoint _ _ s (BasedSpace.smashPoint _ _ t x)), r)
    rw [spaceSmashParameterProductLevel_apply_all, spaceSmash_bond]

/-- The actual reverse parameter-tensor map needs compact Hausdorff
parameters; the spectrum itself is arbitrary. -/
noncomputable def spaceSmashParameterProductInverse (S T : TopCat.{0})
    [CompactSpace S] [T2Space S] [CompactSpace T] [T2Space T] (X : Prespectrum.{0}) :
    spaceSmash (BasedSpace.adjoinPoint (TopCat.of (S × T))) X ⟶
      spaceSmash (BasedSpace.adjoinPoint S) (spaceSmash (BasedSpace.adjoinPoint T) X) where
  level n := (spaceSmashParameterProductInverseLevel S T (X.level n)).map
  point n := (spaceSmashParameterProductInverseLevel S T (X.level n)).point
  bond n z r := by
    refine Quot.inductionOn z ?_
    rintro ⟨p, x⟩
    cases p with
    | inl p =>
      change (spaceSmashParameterProductInverseLevel S T (X.level (n+1))).map
        ((spaceSmash (BasedSpace.adjoinPoint (TopCat.of (S × T))) X).bond n
          (BasedSpace.smashPoint _ _ (.inl p) x, r)) = _
      rw [spaceSmash_bond, spaceSmashParameterProductInverseLevel_apply]
      change _ = (spaceSmash (BasedSpace.adjoinPoint S) (spaceSmash (BasedSpace.adjoinPoint T) X)).bond n
        ((spaceSmashParameterProductInverseLevel S T (X.level n)).map
          (BasedSpace.smashPoint _ _ (.inl p) x), r)
      rw [spaceSmashParameterProductInverseLevel_apply]
      change _ = (spaceSmash (BasedSpace.adjoinPoint S) (spaceSmash (BasedSpace.adjoinPoint T) X)).bond n
        (BasedSpace.smashPoint (BasedSpace.adjoinPoint S) ((spaceSmash (BasedSpace.adjoinPoint T) X).level n)
          (.inl p.1) (BasedSpace.smashPoint (BasedSpace.adjoinPoint T) (X.level n) (.inl p.2) x), r)
      rw [spaceSmash_bond, spaceSmash_bond]
      rfl
    | inr p =>
      cases p
      change (spaceSmashParameterProductInverseLevel S T (X.level (n+1))).map
        ((spaceSmash (BasedSpace.adjoinPoint (TopCat.of (S × T))) X).bond n
          (BasedSpace.smashPoint _ _ (BasedSpace.adjoinPoint (TopCat.of (S × T))).point x, r)) =
        (spaceSmash (BasedSpace.adjoinPoint S) (spaceSmash (BasedSpace.adjoinPoint T) X)).bond n
          ((spaceSmashParameterProductInverseLevel S T (X.level n)).map
            (BasedSpace.smashPoint _ _ (BasedSpace.adjoinPoint (TopCat.of (S × T))).point x), r)
      have hz : BasedSpace.smashPoint (BasedSpace.adjoinPoint (TopCat.of (S × T))) (X.level n)
          (BasedSpace.adjoinPoint (TopCat.of (S × T))).point x =
          ((spaceSmash (BasedSpace.adjoinPoint (TopCat.of (S × T))) X).level n).point :=
        BasedSpace.smashPoint_base_left _ _ _
      rw [hz]
      have hpoint (k : ℕ) : (spaceSmashParameterProductInverseLevel S T (X.level k)).map
          ((spaceSmash (BasedSpace.adjoinPoint (TopCat.of (S × T))) X).level k).point =
          ((spaceSmash (BasedSpace.adjoinPoint S) (spaceSmash (BasedSpace.adjoinPoint T) X)).level k).point :=
        (spaceSmashParameterProductInverseLevel S T (X.level k)).point
      rw [(spaceSmash (BasedSpace.adjoinPoint (TopCat.of (S × T))) X).bond_point,
        hpoint, hpoint]
      exact (Prespectrum.bond_point _ n r).symm

end KIP126.StableHomotopy.Implementation.Prespectrum
