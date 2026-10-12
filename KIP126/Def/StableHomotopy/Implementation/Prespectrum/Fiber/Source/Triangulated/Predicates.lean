module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Iteration.Triangle.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Pretriangulated

universe u

/-- Distinguished triangles are precisely triangles isomorphic to the actual
fiber triangle of a strict prespectrum map. -/
def sourceFiberDistinguished (T : Triangle SourceCategory.{u}) : Prop :=
  ∃ (X Y : Prespectrum.{u}) (f : X ⟶ Y), Nonempty (T ≅ sourceFiberTriangle f)

end KIP126.StableHomotopy.Implementation.Prespectrum
