module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Source.Exact.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Source.Functor

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits

universe u

set_option backward.isDefEq.respectTransparency false

/-- Every morphism of the original stable localization has an actual fiber
sequence exact at all three middle terms on all represented hom groups. -/
theorem source_exists_fiber_sequence {X Y : SourceCategory.{u}} (f : X ⟶ Y) :
    ∃ (F : SourceCategory.{u}) (p : F ⟶ X) (δ : sourceLoopFunctor.obj Y ⟶ F),
      (∀ A : SourceCategory.{u},
        Function.Exact (Preadditive.rightComp A (sourceLoopFunctor.map f))
          (Preadditive.rightComp A δ)) ∧
      (∀ A : SourceCategory.{u},
        Function.Exact (Preadditive.rightComp A δ) (Preadditive.rightComp A p)) ∧
      (∀ A : SourceCategory.{u},
        Function.Exact (Preadditive.rightComp A p) (Preadditive.rightComp A f)) := by
  have hroof : sourceHasRoof f := by rw [sourceHasRoof_all]; trivial
  obtain ⟨B, s, t, hs, hst⟩ := hroof
  letI := stableEquivalences.Q_inverts s hs
  refine ⟨sourceLocalization.obj (fiber t),
    sourceLocalization.map (fiberProjection t) ≫ sourceLocalization.map s,
    sourceLocalization.map (fiberConnecting t), ?_, ?_, ?_⟩
  · intro A h
    change h ≫ sourceLocalization.map (fiberConnecting t) = 0 ↔
      ∃ k, k ≫ sourceLoopFunctor.map f = h
    rw [source_loopMap_fiberConnecting_exact t A h]
    have ht : sourceLoopFunctor.map (sourceLocalization.map s) ≫ sourceLoopFunctor.map f =
        sourceLocalization.map (loopMap t) := by
      rw [← CategoryTheory.Functor.map_comp, hst, sourceLoopFunctor_map]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k ≫ sourceLoopFunctor.map (sourceLocalization.map s),
        by simpa only [Category.assoc, ht] using hk⟩
    · rintro ⟨k, hk⟩
      refine ⟨k ≫ inv (sourceLoopFunctor.map (sourceLocalization.map s)), ?_⟩
      rw [← ht]
      simpa only [Category.assoc, IsIso.inv_hom_id_assoc] using hk
  · intro A h
    change h ≫ (sourceLocalization.map (fiberProjection t) ≫ sourceLocalization.map s) = 0 ↔ _
    rw [← Category.assoc]
    have hz : (h ≫ sourceLocalization.map (fiberProjection t)) ≫ sourceLocalization.map s = 0 ↔
        h ≫ sourceLocalization.map (fiberProjection t) = 0 := by
      constructor
      · intro hh
        apply (cancel_mono (sourceLocalization.map s)).mp
        simpa only [zero_comp] using hh
      · intro hh
        rw [hh, zero_comp]
    rw [hz]
    exact source_fiberConnecting_exact t A h
  · intro A h
    change h ≫ f = 0 ↔ ∃ k, k ≫
      (sourceLocalization.map (fiberProjection t) ≫ sourceLocalization.map s) = h
    constructor
    · intro hh
      have ht : (h ≫ inv (sourceLocalization.map s)) ≫ sourceLocalization.map t = 0 := by
        rw [← hst]
        simpa only [Category.assoc, IsIso.inv_hom_id_assoc] using hh
      obtain ⟨k, hk⟩ := (source_fiberProjection_exact t A _).mp ht
      refine ⟨k, ?_⟩
      rw [← Category.assoc, hk]
      simp
    · rintro ⟨k, rfl⟩
      rw [Category.assoc, Category.assoc, hst, source_fiberProjection_comp]
      change k ≫ sourceLocalization.map (0 : fiber t ⟶ Y.as.obj) = 0
      rw [sourceLocalization.map_zero, comp_zero]

end KIP126.StableHomotopy.Implementation.Prespectrum
