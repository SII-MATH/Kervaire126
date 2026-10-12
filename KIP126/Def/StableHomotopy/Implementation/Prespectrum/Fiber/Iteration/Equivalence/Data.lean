module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Iteration.Homotopy.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyCategory.Homotopy.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u

/-- One actual inverse homotopy removes the initial constant loop. -/
noncomputable def fiberIterationComparisonRetractionHomotopy {X Y : Prespectrum.{u}}
    (f : X ⟶ Y) :
    StrictHomotopy (fiberIterationComparison f ≫ fiberIterationRetraction f)
      (𝟙 (Prespectrum.loop Y)) where
  hom := loopLeftUnitPath (𝟙 (Prespectrum.loop Y))
  zero := (loopLeftUnitPath_zero _).trans (fiberIterationComparison_retraction f).symm
  one := loopLeftUnitPath_one _

/-- The opposite inverse homotopy first reverses the source-path transport,
then removes the initial constant target-path segment. -/
noncomputable def fiberIterationRetractionComparisonHomotopy {X Y : Prespectrum.{u}}
    (f : X ⟶ Y) :
    StrictHomotopy (fiberIterationRetraction f ≫ fiberIterationComparison f)
      (𝟙 (fiber (fiberProjection f))) := by
  let move : StrictHomotopy
      (fiberIterationPaddingHomotopy f ≫ pathEvaluation _ 0)
      (fiberIterationRetraction f ≫ fiberIterationComparison f) :=
    ⟨fiberIterationMoveHomotopy f,fiberIterationHomotopy_zero f,
      fiberIterationMoveHomotopy_one f⟩
  let padding : StrictHomotopy
      (fiberIterationPaddingHomotopy f ≫ pathEvaluation _ 0)
      (𝟙 (fiber (fiberProjection f))) :=
    ⟨fiberIterationPaddingHomotopy f,rfl,fiberIterationPaddingHomotopy_one f⟩
  exact move.symm.trans padding

/-- The displayed actual homotopy inverse gives a specified isomorphism
from the loop object to the iterated fiber in the original source category. -/
noncomputable def sourceFiberIterationIso {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    sourceLocalization.obj (Prespectrum.loop Y) ≅
      sourceLocalization.obj (fiber (fiberProjection f)) where
  hom := sourceLocalization.map (fiberIterationComparison f)
  inv := sourceLocalization.map (fiberIterationRetraction f)
  hom_inv_id := by
    rw [← Functor.map_comp]
    exact (source_map_eq_of_pathHomotopic
      ⟨fiberIterationComparisonRetractionHomotopy f⟩).trans (sourceLocalization.map_id _)
  inv_hom_id := by
    rw [← Functor.map_comp]
    exact (source_map_eq_of_pathHomotopic
      ⟨fiberIterationRetractionComparisonHomotopy f⟩).trans (sourceLocalization.map_id _)

end KIP126.StableHomotopy.Implementation.Prespectrum
