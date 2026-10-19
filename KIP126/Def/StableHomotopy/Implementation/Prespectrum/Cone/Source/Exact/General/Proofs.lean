module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cone.Map.Stability.General.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits

universe u

set_option backward.isDefEq.respectTransparency false

/-- The actual cone of an arbitrary strict map is contravariantly exact in
the original stable localization. Its cofibrant comparison is proved invertible. -/
theorem source_coneInclusion_exact_general {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (A : SourceCategory.{u}) (a : sourceLocalization.obj Y ⟶ A) :
    sourceLocalization.map f ≫ a = 0 ↔
      ∃ b : sourceLocalization.obj (cone f) ⟶ A,
        sourceLocalization.map (coneInclusion f) ≫ b = a := by
  let qX := cubicalReplacementComparison.app X
  let qY := cubicalReplacementComparison.app Y
  let f' := cubicalReplacementFunctor.map f
  have h : f' ≫ qY = qX ≫ f := cubicalReplacementComparison.naturality f
  let c := coneMap qX qY h
  letI := stableEquivalences.Q_inverts qY (cubicalReplacementComparison_stableEquivalence Y)
  letI := stableEquivalences.Q_inverts c (coneMap_stableEquivalence qX qY h
    (cubicalReplacementComparison_stableEquivalence X)
    (cubicalReplacementComparison_stableEquivalence Y))
  have hi : sourceLocalization.map (coneInclusion f') ≫ sourceLocalization.map c =
      sourceLocalization.map qY ≫ sourceLocalization.map (coneInclusion f) := by
    simpa only [sourceLocalization.map_comp] using
      congrArg sourceLocalization.map (coneInclusion_map qX qY h)
  constructor
  · intro ha
    have ha' : sourceLocalization.map f' ≫ (sourceLocalization.map qY ≫ a) = 0 := by
      rw [← Category.assoc, ← sourceLocalization.map_comp, h,
        sourceLocalization.map_comp, Category.assoc, ha, comp_zero]
    obtain ⟨b, hb⟩ := (source_coneInclusion_exact
      (cubicalReplacement_isCubicallyCofibrant X)
      (cubicalReplacement_isCubicallyCofibrant Y) f' A _).mp ha'
    refine ⟨inv (sourceLocalization.map c) ≫ b, (cancel_epi (sourceLocalization.map qY)).mp ?_⟩
    rw [← Category.assoc, ← hi, Category.assoc, IsIso.hom_inv_id_assoc]
    exact hb
  · rintro ⟨b, rfl⟩
    rw [← Category.assoc, source_coneInclusion_comp, zero_comp]

/-- Exactness at the original cone boundary, without object cofibrancy. -/
theorem source_coneBoundary_exact_general {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (A : SourceCategory.{u}) (a : sourceLocalization.obj (cone f) ⟶ A) :
    sourceLocalization.map (coneInclusion f) ≫ a = 0 ↔
      ∃ b : sourceLocalization.obj X.suspension ⟶ A,
        sourceLocalization.map (coneBoundary f) ≫ b = a := by
  letI := stableEquivalences.Q_inverts _ (coneIterationComparison_stableEquivalence f)
  rw [source_coneInclusion_exact_general (coneInclusion f) A a]
  have h : sourceLocalization.map (coneInclusion (coneInclusion f)) ≫
      sourceLocalization.map (coneIterationComparison f) = sourceLocalization.map (coneBoundary f) := by
    rw [← sourceLocalization.map_comp, coneIterationComparison_inclusion]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨inv (sourceLocalization.map (coneIterationComparison f)) ≫ b, ?_⟩
    rw [← h, Category.assoc, IsIso.hom_inv_id_assoc]
    exact hb
  · rintro ⟨b, hb⟩
    refine ⟨sourceLocalization.map (coneIterationComparison f) ≫ b, ?_⟩
    rw [← Category.assoc, h, hb]

end KIP126.StableHomotopy.Implementation.Prespectrum
