module

public import KIP126.Def.StableHomotopy.Implementation.Sphere.Representatives.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

/-- Reflection in a specified coordinate of the original canonical
sphere cube, extended to the original fixed based sphere. -/
noncomputable def sphereCoordinateReflection (n : ℕ) (i : Fin n) :
    sphereLevel n ⟶ sphereLevel n :=
  (genLoop_sphereLevel_map_exists_unique n (sphereLevel n)
    (GenLoop.symmAt i (sphereCube n))).choose

end KIP126.StableHomotopy.Implementation.Prespectrum
