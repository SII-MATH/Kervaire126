module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Composition.Proofs

@[expose] public section

section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u

/-- The first actual fiber maps into the fiber of the composite-fiber
projection, retaining its displayed sliding nullhomotopy. -/
def fiberCompositeComparison {X Y Z : Prespectrum.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    fiber f ⟶ fiber (fiberCompositeProjection f g) :=
  fiberLift (fiberCompositeProjection f g) (fiberCompositeInclusion f g)
    (fiberCompositeNullPath f g) (fiberCompositeNullPath_zero f g) (fiberCompositeNullPath_one f g)

end KIP126.StableHomotopy.Implementation.Prespectrum

end

section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u

@[simp, reassoc] theorem fiberCompositeComparison_projection {X Y Z : Prespectrum.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    fiberCompositeComparison f g ≫ fiberProjection (fiberCompositeProjection f g) =
      fiberCompositeInclusion f g := rfl

@[simp] theorem fiberCompositeComparison_retraction {X Y Z : Prespectrum.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    fiberCompositeComparison f g ≫ fiberCompositeRetraction f g = 𝟙 (fiber f) := rfl

end KIP126.StableHomotopy.Implementation.Prespectrum

end
