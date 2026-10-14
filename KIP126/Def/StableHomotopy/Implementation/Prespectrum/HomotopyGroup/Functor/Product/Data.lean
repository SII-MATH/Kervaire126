module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Functor.Zero.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Product.Source.Proofs
public import Mathlib.Algebra.Category.Grp.Limits

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory CategoryTheory.Limits

universe u

set_option backward.isDefEq.respectTransparency false

/-- The actual stable-group functor carries the displayed finite source
product to a product of the original abelian stable groups. -/
noncomputable def sourceStableHomotopyAddFunctor_productIsLimit
    {J : Type} [Finite J] (X : J → Prespectrum.{u}) (d : ℤ) :
    IsLimit ((sourceStableHomotopyAddFunctor d).mapCone
      (Fan.mk (sourceLocalization.obj (Prespectrum.piPrespectrum X))
        (fun j => sourceLocalization.map (Prespectrum.piProjection X j)))) := by
  refine (Fan.isLimitMapConeEquiv (sourceStableHomotopyAddFunctor d)
    (fun j => sourceLocalization.obj (X j))
    (Fan.mk (sourceLocalization.obj (Prespectrum.piPrespectrum X))
      (fun j => sourceLocalization.map (Prespectrum.piProjection X j)))).symm ?_
  let e := Prespectrum.stablePiAddEquiv X d
  refine Fan.IsLimit.mk _ (fun s => AddCommGrpCat.ofHom
    (e.symm.toAddMonoidHom.comp (AddMonoidHom.pi (fun j => (s.proj j).hom)))) ?_ ?_
  · intro s j
    apply AddCommGrpCat.ext
    intro x
    change Prespectrum.stableHomotopyMap (Prespectrum.piProjection X j) d
      (e.symm (fun j => s.proj j x)) = s.proj j x
    exact congrFun (e.apply_symm_apply (fun j => s.proj j x)) j
  · intro s m hm
    apply AddCommGrpCat.ext
    intro x
    apply e.injective
    funext j
    change Prespectrum.stableHomotopyMap (Prespectrum.piProjection X j) d (m x) =
      e (e.symm (fun j => s.proj j x)) j
    rw [e.apply_symm_apply]
    have h := ConcreteCategory.congr_hom (hm j) x
    change ((sourceStableHomotopyAddFunctor d).map
      (sourceLocalization.map (Prespectrum.piProjection X j))) (m x) = s.proj j x at h
    rw [sourceStableHomotopyAddFunctor_map] at h
    exact h

end KIP126.StableHomotopy.Implementation
