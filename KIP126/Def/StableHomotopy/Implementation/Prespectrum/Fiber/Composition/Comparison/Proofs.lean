module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Composition.Comparison.Data

@[expose] public section

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
