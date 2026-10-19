module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Composition.Triangle.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Source.Triangulated.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
universe u

/-- The actual fourth composition triangle belongs to the isomorphism
closure of standard fiber triangles, by its explicit retained-square comparison. -/
theorem sourceFiberDistinguished_composite {X Y Z : Prespectrum.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    sourceFiberDistinguished (sourceFiberCompositeTriangle f g) :=
  sourceFiberDistinguished_iso (sourceFiberCompositeTriangleIso f g).symm
    (sourceFiberDistinguished_fiber (fiberCompositeProjection f g))

end KIP126.StableHomotopy.Implementation.Prespectrum
