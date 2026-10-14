module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Product.Derived.Comparison
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Functor.Product.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory CategoryTheory.Limits

universe u

set_option backward.isDefEq.respectTransparency false

/-- Arbitrary products of actual stabilized prespectra commute with the
original abelian stable homotopy groups through the actual projections. -/
noncomputable def Prespectrum.stablePiAddEquiv_of_stabilization {J : Type}
    (X : J → Prespectrum.{u}) (hX : ∀ j, (X j).HasBijectiveStabilization) (d : ℤ) :
    StableHomotopy (Prespectrum.piPrespectrum X) d ≃+ ∀ j, StableHomotopy (X j) d where
  toEquiv := Equiv.ofBijective (Prespectrum.stablePiComparison X d)
    (Prespectrum.stablePiComparison_bijective_of_stabilization X hX d)
  map_add' := Prespectrum.stablePiComparison_add X d

/-- The abelian stable homotopy functor takes the displayed actual product
of stabilized objects to the actual product of their abelian groups. -/
noncomputable def sourceStableHomotopyAddFunctor_productIsLimit_of_stabilization
    {J : Type} (X : J → Prespectrum.{u}) (hX : ∀ j, (X j).HasBijectiveStabilization) (d : ℤ) :
    IsLimit ((sourceStableHomotopyAddFunctor d).mapCone
      (Fan.mk (sourceLocalization.obj (Prespectrum.piPrespectrum X))
        (fun j => sourceLocalization.map (Prespectrum.piProjection X j)))) := by
  refine (Fan.isLimitMapConeEquiv (sourceStableHomotopyAddFunctor d)
    (fun j => sourceLocalization.obj (X j))
    (Fan.mk (sourceLocalization.obj (Prespectrum.piPrespectrum X))
      (fun j => sourceLocalization.map (Prespectrum.piProjection X j)))).symm ?_
  let e := Prespectrum.stablePiAddEquiv_of_stabilization X hX d
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
