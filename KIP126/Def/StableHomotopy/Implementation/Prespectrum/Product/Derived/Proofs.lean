module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Product.Derived.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits

universe u

set_option backward.isDefEq.respectTransparency false

/-- The source cone satisfies the genuine universal property for arbitrary
families. Its construction uses the actual replacements, not an assumed limit. -/
noncomputable def sourceDerivedPiFan_isLimit {J : Type} (X : J → SourceCategory.{u}) :
    IsLimit (sourceDerivedPiFan X) := by
  let adj := sourceDerivedPiAdjunction.{u} J
  refine Fan.IsLimit.mk _ (fun s => (adj.homEquiv s.pt X) (fun j => s.proj j)) ?_ ?_
  · intro s j
    have h := (adj.homEquiv s.pt X).symm_apply_apply (fun j => s.proj j)
    rw [Adjunction.homEquiv_counit] at h
    exact congrFun h j
  · intro s m hm
    apply (adj.homEquiv s.pt X).symm.injective
    rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
    exact funext hm

/-- The ordinary stable localization has actual products indexed by any
small type, in particular countable products. -/
instance sourceHasProductsOfShape (J : Type) : HasProductsOfShape J SourceCategory.{u} := by
  refine ⟨fun F => ?_⟩
  letI : HasLimit (Discrete.functor (F.obj ∘ Discrete.mk)) :=
    ⟨⟨sourceDerivedPiFan (F.obj ∘ Discrete.mk), sourceDerivedPiFan_isLimit _⟩⟩
  exact hasLimit_of_iso Discrete.natIsoFunctor.symm

end KIP126.StableHomotopy.Implementation.Prespectrum
