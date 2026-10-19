module

public import KIP126.Def.StableHomotopy.Implementation.Completion.Locality.Predicates
public import KIP126.Def.StableHomotopy.Implementation.Completion.Shift.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Source.Map.Equivalence.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Source.Adjunction.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory

set_option backward.isDefEq.respectTransparency false

theorem SourceIsHF2Local.of_iso {X Y : SourceCategory.{0}} (e : X ≅ Y)
    (hY : SourceIsHF2Local Y) : SourceIsHF2Local X := by
  intro A B f hf
  constructor
  · intro a b hab
    apply (cancel_mono e.hom).mp
    apply (hY f hf).injective
    simpa only [Category.assoc] using congrArg (fun z => z ≫ e.hom) hab
  · intro a
    obtain ⟨b,hb⟩ := (hY f hf).surjective (a ≫ e.hom)
    change f ≫ b = a ≫ e.hom at hb
    refine ⟨b ≫ e.inv, ?_⟩
    change f ≫ (b ≫ e.inv) = a
    rw [← Category.assoc, hb, Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem SourceIsHF2Local.suspension {X : SourceCategory.{0}} (hX : SourceIsHF2Local X) :
    SourceIsHF2Local (Prespectrum.sourceSuspensionFunctor.obj X) := by
  rcases X with ⟨⟨X⟩⟩
  exact Prespectrum.IsHF2Local.suspension hX

theorem SourceIsHF2Local.desuspension {X : SourceCategory.{0}} (hX : SourceIsHF2Local X) :
    SourceIsHF2Local (Prespectrum.sourceDesuspensionFunctor.obj X) := by
  rcases X with ⟨⟨X⟩⟩
  exact Prespectrum.IsHF2Local.desuspension hX

/-- Actual compact-open loops of a local prespectrum remain local. -/
theorem Prespectrum.IsHF2Local.loop {X : Prespectrum.{0}} (hX : X.IsHF2Local) :
    (Prespectrum.loop X).IsHF2Local :=
  SourceIsHF2Local.of_iso (sourceLoopComparisonIso X) hX.desuspension

/-- The actual retained-path fiber of a map between HF₂-local prespectra
is local, by its represented exact sequence and the additive five lemma. -/
theorem Prespectrum.IsHF2Local.fiber {X Y : Prespectrum.{0}} (k : X ⟶ Y)
    (hX : X.IsHF2Local) (hY : Y.IsHF2Local) : (Prespectrum.fiber k).IsHF2Local := by
  intro A B f hf
  exact AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
    (Preadditive.rightComp B (sourceLocalization.map (loopMap k)))
    (Preadditive.rightComp B (sourceLocalization.map (fiberConnecting k)))
    (Preadditive.rightComp B (sourceLocalization.map (fiberProjection k)))
    (Preadditive.rightComp B (sourceLocalization.map k))
    (Preadditive.rightComp A (sourceLocalization.map (loopMap k)))
    (Preadditive.rightComp A (sourceLocalization.map (fiberConnecting k)))
    (Preadditive.rightComp A (sourceLocalization.map (fiberProjection k)))
    (Preadditive.rightComp A (sourceLocalization.map k))
    (Preadditive.leftComp (sourceLocalization.obj (Prespectrum.loop X)) f)
    (Preadditive.leftComp (sourceLocalization.obj (Prespectrum.loop Y)) f)
    (Preadditive.leftComp (sourceLocalization.obj (Prespectrum.fiber k)) f)
    (Preadditive.leftComp (sourceLocalization.obj X) f)
    (Preadditive.leftComp (sourceLocalization.obj Y) f)
    (by ext z; change (f ≫ z) ≫ _ = f ≫ z ≫ _; exact Category.assoc _ _ _)
    (by ext z; change (f ≫ z) ≫ _ = f ≫ z ≫ _; exact Category.assoc _ _ _)
    (by ext z; change (f ≫ z) ≫ _ = f ≫ z ≫ _; exact Category.assoc _ _ _)
    (by ext z; change (f ≫ z) ≫ _ = f ≫ z ≫ _; exact Category.assoc _ _ _)
    (source_loopMap_fiberConnecting_hom_exact k B)
    (source_fiberConnecting_hom_exact k B) (source_fiberProjection_hom_exact k B)
    (source_loopMap_fiberConnecting_hom_exact k A)
    (source_fiberConnecting_hom_exact k A) (source_fiberProjection_hom_exact k A)
    (hX.loop f hf).surjective (hY.loop f hf) (hX f hf) (hY f hf).injective

end KIP126.StableHomotopy.Implementation
