module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Product.Localization.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits

universe u

variable {J : Type} [Finite J]

/-- The displayed projections form a product of the actual source objects. -/
noncomputable def sourceProductIsLimit (X : J → Prespectrum.{u}) :
    IsLimit (Fan.mk (sourceLocalization.obj (piPrespectrum X))
      (fun j => sourceLocalization.map (piProjection X j))) :=
  (Fan.isLimitMapConeEquiv sourceLocalization X (piFan X)) (sourcePiFan_isLimit X)

/-- Pair arbitrary localized morphisms into the displayed pointwise product. -/
noncomputable def sourcePiLift (X : J → Prespectrum.{u}) {A : SourceCategory.{u}}
    (f : ∀ j, A ⟶ sourceLocalization.obj (X j)) :
    A ⟶ sourceLocalization.obj (piPrespectrum X) :=
  Fan.IsLimit.lift (sourceProductIsLimit X) f

/-- The displayed source products act on arbitrary localized maps. -/
noncomputable def sourcePiMap {X Y : J → Prespectrum.{u}}
    (f : ∀ j, sourceLocalization.obj (X j) ⟶ sourceLocalization.obj (Y j)) :
    sourceLocalization.obj (piPrespectrum X) ⟶ sourceLocalization.obj (piPrespectrum Y) :=
  sourcePiLift Y (fun j => sourceLocalization.map (piProjection X j) ≫ f j)

end KIP126.StableHomotopy.Implementation.Prespectrum
