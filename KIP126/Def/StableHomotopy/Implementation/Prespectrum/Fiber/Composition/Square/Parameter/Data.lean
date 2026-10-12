module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Composition.Square.Data
public import KIP126.Def.Topology.Cube.Square.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology KIP126.Topology.Cube
open scoped unitInterval
universe u

/-- Pad every horizontal path by a constant terminal segment and remove
that padding continuously, retaining the source path. -/
noncomputable def fiberCompositePaddingSquare {X Y Z : Prespectrum.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    C(((I × (fiber (fiberCompositeProjection f g)).level n) × I) × I,Z.level n) :=
  ⟨fun z => (z.1.1.2.val.2 z.1.2).val.2 (unitInterval.qRight (z.2,z.1.1.1)),by fun_prop⟩

/-- Slide the padded horizontal edges across the retained square to
the padded source-path image, preserving the two zero edges throughout. -/
noncomputable def fiberCompositeMoveSquare {X Y Z : Prespectrum.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    C(((I × (fiber (fiberCompositeProjection f g)).level n) × I) × I,Z.level n) :=
  ⟨fun z => (z.1.1.2.val.2
      (Set.Icc.convexComb z.1.2 (Set.Icc.convexComb z.1.2 1 (advancedCoordinate z.2)) z.1.1.1)).val.2
        (Set.Icc.convexComb (advancedCoordinate z.2) (delayedCoordinate z.2) z.1.1.1),by fun_prop⟩

end KIP126.StableHomotopy.Implementation.Prespectrum
