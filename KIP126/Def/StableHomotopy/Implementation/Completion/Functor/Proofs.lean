module

public import KIP126.Def.StableHomotopy.Implementation.Completion.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation
open CategoryTheory Prespectrum
set_option backward.isDefEq.respectTransparency false

/-- The actual reflection preserves mod-two cohomology equivalences, by
naturality of its unit and its tested universal property. -/
theorem CompletionModel.map_hf2Equivalence (M : CompletionModel)
    {X Y : Prespectrum.{0}} (f : X ⟶ Y)
    (hf : HF2Equivalences (sourceLocalization.map f)) :
    HF2Equivalences (sourceLocalization.map (M.replacement.map f)) := by
  have hn : sourceLocalization.map (M.unit.app X) ≫ sourceLocalization.map (M.replacement.map f) =
      sourceLocalization.map f ≫ sourceLocalization.map (M.unit.app Y) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg sourceLocalization.map (M.unit.naturality f).symm
  intro d
  have hX := M.unit_hf2Equivalence X d
  have hY := M.unit_hf2Equivalence Y d
  constructor
  · intro a b hab
    apply hY.injective
    apply (hf d).injective
    change sourceLocalization.map f ≫ (sourceLocalization.map (M.unit.app Y) ≫ a) =
      sourceLocalization.map f ≫ (sourceLocalization.map (M.unit.app Y) ≫ b)
    rw [← Category.assoc, ← Category.assoc, ← hn, Category.assoc, Category.assoc]
    exact congrArg (fun c => sourceLocalization.map (M.unit.app X) ≫ c) hab
  · intro a
    obtain ⟨b,hb⟩ := (hf d).surjective (sourceLocalization.map (M.unit.app X) ≫ a)
    obtain ⟨c,hc⟩ := hY.surjective b
    refine ⟨c,hX.injective ?_⟩
    change sourceLocalization.map (M.unit.app X) ≫
      (sourceLocalization.map (M.replacement.map f) ≫ c) = sourceLocalization.map (M.unit.app X) ≫ a
    rw [← Category.assoc, hn, Category.assoc]
    exact (congrArg (fun b => sourceLocalization.map f ≫ b) hc).trans hb

/-- Point-set stable equivalences stay invertible after the specified
HF₂ reflection. -/
theorem completedLocalization_map_isIso_of_stableEquivalence
    {X Y : Prespectrum.{0}} (f : X ⟶ Y) (hf : stableEquivalences f) :
    IsIso (completedLocalization.map f) := by
  letI : IsIso (sourceLocalization.map f) := stableEquivalences.Q_inverts _ hf
  have hf' : HF2Equivalences (sourceLocalization.map f) := by
    intro d
    constructor
    · intro a b hab
      exact (cancel_epi (sourceLocalization.map f)).mp hab
    · intro a
      refine ⟨inv (sourceLocalization.map f) ≫ a, ?_⟩
      exact IsIso.hom_inv_id_assoc _ _
  have h := Prespectrum.IsHF2Local.isIso_of_hf2Equivalence
    (completionModel.isLocal X) (completionModel.isLocal Y)
    (sourceLocalization.map (completionModel.replacement.map f))
    (completionModel.map_hf2Equivalence f hf')
  obtain ⟨g,hg,hg'⟩ := h.out
  exact ⟨⟨g,hg,hg'⟩⟩

end KIP126.StableHomotopy.Implementation
