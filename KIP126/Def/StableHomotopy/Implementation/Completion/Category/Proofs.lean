module

public import KIP126.Def.StableHomotopy.Implementation.Completion.Category.Data
public import KIP126.Def.StableHomotopy.Implementation.Completion.Product.Category
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Zero.Instances

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

/-- An actual source zero object satisfies HF₂ locality because all maps
into it are unique. -/
theorem Prespectrum.isHF2Local_of_source_isZero (X : Prespectrum.{0})
    (hX : IsZero (sourceLocalization.obj X)) : X.IsHF2Local := by
  intro A B f _
  constructor
  · intro a b _
    exact hX.eq_of_tgt a b
  · intro a
    exact ⟨hX.from_ B, hX.eq_of_tgt _ a⟩

namespace CompletedSpectrum

instance toSource_full : toSource.Full where
  map_surjective f := ⟨f, rfl⟩

instance toSource_faithful : toSource.Faithful where
  map_injective h := h

/-- The inclusion carries the displayed local product cone to an actual
limit cone in the ordinary source category. -/
noncomputable def toSource_piFan_isLimit {J : Type} [Finite J]
    (X : J → CompletedSpectrum) : IsLimit (toSource.mapCone (piFan X)) :=
  (Fan.isLimitMapConeEquiv toSource X (piFan X)).symm
    ((Fan.isLimitMapConeEquiv sourceLocalization (fun j => (X j).spectrum)
      (Prespectrum.piFan (fun j => (X j).spectrum)))
      (Prespectrum.sourcePiFan_isLimit (fun j => (X j).spectrum)))

instance toSource_preservesProduct {J : Type} [Finite J]
    (X : J → CompletedSpectrum) : PreservesLimit (Discrete.functor X) toSource :=
  preservesLimit_of_preserves_limit_cone (piFan_isLimit X) (toSource_piFan_isLimit X)

instance toSource_preservesProductsOfShape (J : Type) [Finite J] :
    PreservesLimitsOfShape (Discrete J) toSource where
  preservesLimit := preservesLimit_of_iso_diagram toSource Discrete.natIsoFunctor.symm

instance toSource_preservesFiniteProducts : PreservesFiniteProducts toSource :=
  ⟨fun _ => inferInstance⟩

end CompletedSpectrum
end KIP126.StableHomotopy.Implementation
