module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Composition.Square.Parameter.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
universe u

/-- Remove the terminal padding of every horizontal edge of the retained
square, as an actual strict based prespectrum homotopy. -/
noncomputable def fiberCompositePaddingHomotopy {X Y Z : Prespectrum.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    fiber (fiberCompositeProjection f g) ⟶ pathPrespectrum (fiber (fiberCompositeProjection f g)) :=
  fiberCompositeSquareHomotopy f g (fiberCompositePaddingSquare f g)
    (fiberCompositePaddingSquare_start f g) (fiberCompositePaddingSquare_end f g)
    (fiberCompositePaddingSquare_top f g) (by intros; rfl) (by intros; rfl)

/-- Slide the padded horizontal edges to the image of the source path,
as an actual strict based prespectrum homotopy. -/
noncomputable def fiberCompositeMoveHomotopy {X Y Z : Prespectrum.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    fiber (fiberCompositeProjection f g) ⟶ pathPrespectrum (fiber (fiberCompositeProjection f g)) :=
  fiberCompositeSquareHomotopy f g (fiberCompositeMoveSquare f g)
    (fiberCompositeMoveSquare_start f g) (fiberCompositeMoveSquare_end f g)
    (fiberCompositeMoveSquare_top f g) (by intros; rfl) (by intros; rfl)

end KIP126.StableHomotopy.Implementation.Prespectrum
