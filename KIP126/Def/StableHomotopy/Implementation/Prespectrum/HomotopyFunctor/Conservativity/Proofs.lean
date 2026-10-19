module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Localization.Roofs.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory

universe u

set_option backward.isDefEq.respectTransparency false

/-- The original integer stable homotopy functors jointly detect
isomorphisms of every localized source morphism, not only strict maps. -/
theorem source_isIso_iff_stableHomotopy_bijective {X Y : SourceCategory.{u}}
    (f : X ⟶ Y) :
    IsIso f ↔ ∀ d : ℤ, Function.Bijective ((sourceStableHomotopyFunctor d).map f) := by
  constructor
  · intro hf d
    letI := hf
    exact (CategoryTheory.isIso_iff_bijective _).mp inferInstance
  · intro hf
    have hroof : Prespectrum.sourceHasRoof f := by
      rw [Prespectrum.sourceHasRoof_all]
      trivial
    obtain ⟨A, s, t, hs, hst⟩ := hroof
    letI := Prespectrum.stableEquivalences.Q_inverts s hs
    have ht : Prespectrum.stableEquivalences t := by
      intro d
      letI := (CategoryTheory.isIso_iff_bijective _).mpr (hf d)
      apply (CategoryTheory.bijective_iff_isIso_ofHom _).mpr
      rw [← sourceStableHomotopyFunctor_map t d, ← hst, CategoryTheory.Functor.map_comp]
      infer_instance
    letI := Prespectrum.stableEquivalences.Q_inverts t ht
    haveI : IsIso (sourceLocalization.map s ≫ f) := by rw [hst]; infer_instance
    exact IsIso.of_isIso_comp_left (sourceLocalization.map s) f

end KIP126.StableHomotopy.Implementation
