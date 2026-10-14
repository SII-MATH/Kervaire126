module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Localization.Roofs.Predicates
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyPullback.Stability.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

universe u

set_option backward.isDefEq.respectTransparency false

/-- Strict maps have the identity-denominator roof. -/
theorem sourceHasRoof_map {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    sourceHasRoof (sourceLocalization.map f) := by
  refine ⟨X, 𝟙 X, f, ?_, ?_⟩
  · apply (stableEquivalence_iff_source_isIso _).mpr
    rw [CategoryTheory.Functor.map_id]
    infer_instance
  · rw [CategoryTheory.Functor.map_id, Category.id_comp]

/-- The formal inverse of a stable equivalence has its defining strict roof. -/
theorem sourceHasRoof_inverse {X Y : Prespectrum.{u}} (s : X ⟶ Y)
    (hs : stableEquivalences s) :
    sourceHasRoof (Localization.Construction.wInv s hs) := by
  refine ⟨X, s, 𝟙 X, hs, ?_⟩
  exact (Localization.Construction.wIso s hs).hom_inv_id.trans
    (sourceLocalization.map_id X).symm

/-- Actual homotopy pullback composes roofs in the original localization.
Its square is allowed to commute by the constructed strict homotopy. -/
instance sourceHasRoof_stableUnderComposition : sourceHasRoof.{u}.IsStableUnderComposition where
  comp_mem := by
    intro X Y Z f g hf hg
    rcases X with ⟨⟨X⟩⟩
    rcases Y with ⟨⟨Y⟩⟩
    rcases Z with ⟨⟨Z⟩⟩
    obtain ⟨A, s, t, hs, ht⟩ := hf
    obtain ⟨B, u, v, hu, hv⟩ := hg
    let P := homotopyPullback u t
    let a : P ⟶ B := homotopyPullbackFst u t
    let b : P ⟶ A := homotopyPullbackSnd u t
    have hb : stableEquivalences b := homotopyPullbackSnd_stableEquivalence u t hu
    refine ⟨P, b ≫ s, a ≫ v, ?_, ?_⟩
    · apply (stableEquivalence_iff_source_isIso _).mpr
      letI := stableEquivalences.Q_inverts b hb
      letI := stableEquivalences.Q_inverts s hs
      rw [CategoryTheory.Functor.map_comp]
      infer_instance
    · rw [CategoryTheory.Functor.map_comp, Category.assoc, ← Category.assoc _ f g,
        ht, ← Category.assoc]
      have hc : sourceLocalization.map b ≫ sourceLocalization.map t =
          sourceLocalization.map a ≫ sourceLocalization.map u :=
        (source_homotopyPullback_comm u t).symm
      rw [hc, Category.assoc, hv, ← CategoryTheory.Functor.map_comp]

/-- Every original source morphism has a strict right-roof representation.
This existence statement uses actual homotopy pullbacks and does not assume
a strict calculus of fractions on the point-set category. -/
theorem sourceHasRoof_all : sourceHasRoof.{u} = ⊤ :=
  Localization.Construction.morphismProperty_eq_top sourceHasRoof
    (fun {X Y} f => sourceHasRoof_map f) (fun {X Y} s hs => sourceHasRoof_inverse s hs)

/-- Concrete strict spans represent all morphisms between specified source
objects, including composites of formal inverses. -/
theorem source_morphism_exists_roof {X Y : Prespectrum.{u}}
    (f : sourceLocalization.obj X ⟶ sourceLocalization.obj Y) :
    ∃ (A : Prespectrum.{u}) (s : A ⟶ X) (t : A ⟶ Y),
      stableEquivalences s ∧ sourceLocalization.map s ≫ f = sourceLocalization.map t := by
  have h : sourceHasRoof f := by rw [sourceHasRoof_all]; trivial
  exact h

end KIP126.StableHomotopy.Implementation.Prespectrum
