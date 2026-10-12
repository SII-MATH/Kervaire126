module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Stabilized.Product.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Stabilized.Localizer.Pi.Source.Proofs
public import Mathlib.CategoryTheory.Localization.Adjunction

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits

universe u

set_option backward.isDefEq.respectTransparency false

/-- The actual stabilized product functor as a morphism of localizers. -/
def stabilizedPiLocalizer (J : Type) :
    LocalizerMorphism (MorphismProperty.pi (fun _ : J => stabilizedStableEquivalences.{u}))
      stabilizedStableEquivalences where
  functor := stabilizedPiFunctor J
  map _ _ f hf := stabilizedPiFunctor_map_stableEquivalence f hf

/-- The genuine derived product functor on the fixed ordinary source category. -/
noncomputable def sourceDerivedPiFunctor (J : Type) :
    (J → SourceCategory.{u}) ⥤ SourceCategory.{u} :=
  (stabilizedPiLocalizer J).localizedFunctor
    (Functor.pi (fun _ : J => stabilizedInclusion ⋙ t1Inclusion ⋙ sourceLocalization))
    (stabilizedInclusion ⋙ t1Inclusion ⋙ sourceLocalization)

/-- The actual product adjunction descends through the proved localization
equivalences to the fixed source category. -/
noncomputable def sourceDerivedPiAdjunction (J : Type) :
    Functor.pi' (fun _ : J => 𝟭 SourceCategory.{u}) ⊣ sourceDerivedPiFunctor J := by
  let L := stabilizedInclusion.{u} ⋙ t1Inclusion ⋙ sourceLocalization
  let Lp := Functor.pi (fun _ : J => L)
  let Δ := Functor.pi' (fun _ : J => 𝟭 StabilizedPrespectrum.{u})
  let Δ' := Functor.pi' (fun _ : J => 𝟭 SourceCategory.{u})
  letI : CatCommSq Δ L Lp Δ' := ⟨Iso.refl _⟩
  letI : CatCommSq (stabilizedPiFunctor J) Lp L (sourceDerivedPiFunctor J) :=
    inferInstanceAs (CatCommSq (stabilizedPiLocalizer J).functor Lp L
      ((stabilizedPiLocalizer J).localizedFunctor Lp L))
  exact (stabilizedPiAdjunction J).localization L stabilizedStableEquivalences
    Lp (MorphismProperty.pi (fun _ : J => stabilizedStableEquivalences)) Δ'
      (sourceDerivedPiFunctor J)

/-- The explicit product cone provided by the actual derived adjunction. -/
noncomputable def sourceDerivedPiFan {J : Type} (X : J → SourceCategory.{u}) : Fan X :=
  Fan.mk ((sourceDerivedPiFunctor J).obj X) (fun j => (sourceDerivedPiAdjunction J).counit.app X j)

end KIP126.StableHomotopy.Implementation.Prespectrum
