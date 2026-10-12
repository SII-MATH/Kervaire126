module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Composition.Equivalence.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u

/-- The actual composite-fiber comparison is a stable equivalence for
every composable pair, with no lifting or convergence premise. -/
theorem fiberCompositeComparison_stableEquivalence {X Y Z : Prespectrum.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    stableEquivalences (fiberCompositeComparison f g) :=
  (stableEquivalence_iff_source_isIso _).mpr
    (inferInstance : IsIso (sourceFiberCompositeIso f g).hom)

theorem fiberCompositeRetraction_stableEquivalence {X Y Z : Prespectrum.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    stableEquivalences (fiberCompositeRetraction f g) :=
  (stableEquivalence_iff_source_isIso _).mpr
    (inferInstance : IsIso (sourceFiberCompositeIso f g).inv)

@[simp, reassoc] theorem sourceFiberCompositeIso_projection {X Y Z : Prespectrum.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (sourceFiberCompositeIso f g).hom ≫
        sourceLocalization.map (fiberProjection (fiberCompositeProjection f g)) =
      sourceLocalization.map (fiberCompositeInclusion f g) := by
  change sourceLocalization.map (fiberCompositeComparison f g) ≫ _ = _
  rw [← Functor.map_comp,fiberCompositeComparison_projection]

end KIP126.StableHomotopy.Implementation.Prespectrum
