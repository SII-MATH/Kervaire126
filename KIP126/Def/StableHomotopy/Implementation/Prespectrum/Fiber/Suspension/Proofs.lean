module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Loop.Iso.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Source.Map.Existence.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Iteration.Triangle.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Source.Adjunction.Equivalence.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

universe u

set_option backward.isDefEq.respectTransparency false

/-- The actual suspension and fiber constructions commute in the original
source by a specified-existence isomorphism preserving the projection. -/
theorem source_suspension_fiber_iso_exists {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    ∃ e : sourceSuspensionFunctor.obj (sourceLocalization.obj (fiber f)) ≅
      sourceLocalization.obj (fiber (suspensionMap f)),
      e.hom ≫ sourceLocalization.map (fiberProjection (suspensionMap f)) =
        sourceSuspensionFunctor.map (sourceLocalization.map (fiberProjection f)) := by
  have hn : sourceLocalization.map f ≫
        (sourceSuspensionLoopUnitIso.app (sourceLocalization.obj Y)).hom =
      (sourceSuspensionLoopUnitIso.app (sourceLocalization.obj X)).hom ≫
        sourceLocalization.map (loopMap (suspensionMap f)) := by
    have h := sourceSuspensionLoopUnitIso.hom.naturality (sourceLocalization.map f)
    change sourceLocalization.map f ≫ sourceSuspensionLoopUnitIso.hom.app
        (sourceLocalization.obj Y) = sourceSuspensionLoopUnitIso.hom.app
        (sourceLocalization.obj X) ≫ sourceLoopFunctor.map
          (sourceSuspensionFunctor.map (sourceLocalization.map f)) at h
    rw [sourceSuspensionFunctor_map, sourceLoopFunctor_map] at h
    exact h
  obtain ⟨a, ha, _⟩ := source_fiberIso_exists f (loopMap (suspensionMap f))
    (sourceSuspensionLoopUnitIso.app (sourceLocalization.obj X))
    (sourceSuspensionLoopUnitIso.app (sourceLocalization.obj Y)) hn
  let b : sourceLocalization.obj (fiber f) ≅
      sourceLoopFunctor.obj (sourceLocalization.obj (fiber (suspensionMap f))) :=
    a ≪≫ sourceLocalization.mapIso (fiberLoopIso (suspensionMap f))
  have hb : b.hom ≫ sourceLoopFunctor.map
      (sourceLocalization.map (fiberProjection (suspensionMap f))) =
        sourceLocalization.map (fiberProjection f) ≫
          (sourceSuspensionLoopUnitIso.app (sourceLocalization.obj X)).hom := by
    change (a.hom ≫ sourceLocalization.map (fiberLoopToLoopFiber (suspensionMap f))) ≫
      sourceLocalization.map (loopMap (fiberProjection (suspensionMap f))) = _
    rw [Category.assoc, ← Functor.map_comp,
      fiberLoopToLoopFiber_projection]
    exact ha
  let e := sourceSuspensionFunctor.mapIso b ≪≫
    sourceSuspensionLoopCounitIso.app (sourceLocalization.obj (fiber (suspensionMap f)))
  refine ⟨e, ?_⟩
  change (sourceSuspensionFunctor.map b.hom ≫
    sourceSuspensionLoopAdjunction.counit.app
      (sourceLocalization.obj (fiber (suspensionMap f)))) ≫
      sourceLocalization.map (fiberProjection (suspensionMap f)) = _
  have hc := sourceSuspensionLoopAdjunction.counit.naturality
    (sourceLocalization.map (fiberProjection (suspensionMap f)))
  change sourceSuspensionFunctor.map (sourceLoopFunctor.map
      (sourceLocalization.map (fiberProjection (suspensionMap f)))) ≫
        sourceSuspensionLoopAdjunction.counit.app (sourceLocalization.obj X.suspension) =
    sourceSuspensionLoopAdjunction.counit.app
        (sourceLocalization.obj (fiber (suspensionMap f))) ≫
      sourceLocalization.map (fiberProjection (suspensionMap f)) at hc
  rw [Category.assoc, ← hc]
  rw [← Functor.map_comp_assoc, hb, Functor.map_comp, Category.assoc]
  change sourceSuspensionFunctor.map (sourceLocalization.map (fiberProjection f)) ≫
      (sourceSuspensionFunctor.map (sourceSuspensionLoopAdjunction.unit.app
        (sourceLocalization.obj X)) ≫ sourceSuspensionLoopAdjunction.counit.app _) = _
  rw [sourceSuspensionLoopAdjunction.left_triangle_components, Category.comp_id]

end KIP126.StableHomotopy.Implementation.Prespectrum
