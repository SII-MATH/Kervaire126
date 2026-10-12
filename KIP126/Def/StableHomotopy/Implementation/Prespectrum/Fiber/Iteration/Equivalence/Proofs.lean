module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Iteration.Equivalence.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u

/-- The actual loop-to-second-fiber map is a stable equivalence, for every
strict prespectrum map, proved by its displayed strict homotopy inverse. -/
theorem fiberIterationComparison_stableEquivalence {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    stableEquivalences (fiberIterationComparison f) :=
  (stableEquivalence_iff_source_isIso _).mpr
    (inferInstance : IsIso (sourceFiberIterationIso f).hom)

/-- The explicit opposite map is also an actual stable equivalence. -/
theorem fiberIterationRetraction_stableEquivalence {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    stableEquivalences (fiberIterationRetraction f) :=
  (stableEquivalence_iff_source_isIso _).mpr
    (inferInstance : IsIso (sourceFiberIterationIso f).inv)

@[simp, reassoc] theorem sourceFiberIterationIso_projection {X Y : Prespectrum.{u}}
    (f : X ⟶ Y) :
    (sourceFiberIterationIso f).hom ≫ sourceLocalization.map (fiberProjection (fiberProjection f)) =
      sourceLocalization.map (fiberConnecting f) := by
  change sourceLocalization.map (fiberIterationComparison f) ≫ _ = _
  rw [← Functor.map_comp,fiberIterationComparison_projection]

end KIP126.StableHomotopy.Implementation.Prespectrum
