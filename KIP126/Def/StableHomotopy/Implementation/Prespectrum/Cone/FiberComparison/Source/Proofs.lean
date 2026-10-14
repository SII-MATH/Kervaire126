module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cone.FiberComparison.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cone.Iteration.Stability.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Source.Adjunction.Equivalence.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Source.Exact.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cone.Source.Exact.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits

universe u

set_option backward.isDefEq.respectTransparency false

/-- The original two-cylinder Puppe loop is a stable equivalence for every
strict map, by the actual suspension-loop unit and the actual double-cone inverse. -/
theorem source_coneIterationLoop_isIso {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    IsIso (sourceLocalization.map (coneIterationLoop f)) := by
  have h : suspensionLoopCurry (𝟙 X.suspension) ≫ loopMap (coneIterationInverse f) =
      coneIterationLoop f := by
    rw [← suspensionLoopCurry_natural_right, Category.id_comp]
    exact suspensionLoopCurry_uncurry _
  letI := source_suspensionLoopCurry_id_isIso X
  letI := stableEquivalences.Q_inverts _
    (loopMap_stableEquivalence _ (coneIterationInverse_stableEquivalence f))
  rw [← h, sourceLocalization.map_comp]
  infer_instance

/-- The actual fiber of the literal cone inclusion projects through the
original source map after stable localization, without a cofibrancy premise. -/
theorem source_fiber_coneInclusion_projection_factors {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    ∃ g : sourceLocalization.obj (fiber (coneInclusion f)) ⟶ sourceLocalization.obj X,
      g ≫ sourceLocalization.map f =
        sourceLocalization.map (fiberProjection (coneInclusion f)) := by
  let a := sourceLocalization.map (coneIterationLoop f)
  let b := sourceLocalization.map (fiberConeLoop (coneInclusion f))
  let c := sourceLocalization.map (loopMap (coneBoundary (coneInclusion f)))
  let v := sourceLocalization.map
    (suspensionLoopCurry (𝟙 Y.suspension) ≫ loopInverse Y.suspension)
  letI : IsIso a := source_coneIterationLoop_isIso f
  letI : IsIso (loopInverse Y.suspension) :=
    ⟨⟨loopInverse Y.suspension, loopInverse_twice _, loopInverse_twice _⟩⟩
  letI := source_suspensionLoopCurry_id_isIso Y
  have hv : IsIso v := by dsimp [v]; rw [sourceLocalization.map_comp]; infer_instance
  letI := hv
  have ha : a ≫ c = sourceLocalization.map f ≫ v := by
    simpa only [a, c, v, sourceLocalization.map_comp, Category.assoc] using
      source_coneIterationLoop_boundary f
  have hb : b ≫ c = sourceLocalization.map (fiberProjection (coneInclusion f)) ≫ v := by
    simpa only [b, c, v, sourceLocalization.map_comp, Category.assoc] using
      source_fiberConeLoop_boundary (coneInclusion f)
  refine ⟨b ≫ inv a, (cancel_mono v).mp ?_⟩
  rw [Category.assoc]
  calc
    (b ≫ inv a) ≫ sourceLocalization.map f ≫ v = b ≫ inv a ≫ (a ≫ c) := by
      rw [Category.assoc, ha]
    _ = b ≫ c := by simp
    _ = sourceLocalization.map (fiberProjection (coneInclusion f)) ≫ v := hb

/-- Actual covariant exactness at the target of every literal cone sequence.
The original map and cone inclusion are retained, with no replacement hypothesis. -/
theorem source_coneInclusion_postcomp_exact {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (A : SourceCategory.{u}) (a : A ⟶ sourceLocalization.obj Y) :
    a ≫ sourceLocalization.map (coneInclusion f) = 0 ↔
      ∃ b : A ⟶ sourceLocalization.obj X, b ≫ sourceLocalization.map f = a := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := (source_fiberProjection_exact (coneInclusion f) A a).mp h
    obtain ⟨g, hg⟩ := source_fiber_coneInclusion_projection_factors f
    exact ⟨k ≫ g, by rw [Category.assoc, hg, hk]⟩
  · rintro ⟨b, rfl⟩
    rw [Category.assoc, source_coneInclusion_comp, comp_zero]

end KIP126.StableHomotopy.Implementation.Prespectrum
