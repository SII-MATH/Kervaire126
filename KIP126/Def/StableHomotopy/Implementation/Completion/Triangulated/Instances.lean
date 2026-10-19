module

public import KIP126.Def.StableHomotopy.Implementation.Completion.Triangulated.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.CompletedSpectrum

open CategoryTheory

/-- Inclusion preserves the actual distinguished triangles by their
definition in the existing local category. -/
instance toSource_isTriangulated : toSource.IsTriangulated where
  map_distinguished _ hT := hT

/-- The local category satisfies the octahedron axiom by its fully faithful
triangulated inclusion into the actual stable source. -/
instance isTriangulated : IsTriangulated CompletedSpectrum :=
  IsTriangulated.of_fully_faithful_triangulated_functor toSource

end KIP126.StableHomotopy.Implementation.CompletedSpectrum
