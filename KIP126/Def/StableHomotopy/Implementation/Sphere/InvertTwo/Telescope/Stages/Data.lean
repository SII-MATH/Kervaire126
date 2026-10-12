module

public import KIP126.Def.StableHomotopy.Implementation.Sphere.InvertTwo.Bond.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Sphere.Representatives.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Representation.Additive.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory

/-- The actual n-th sphere cube, regarded in the original doubled-bond
sphere and represented by a morphism from the specified source S⁰. -/
noncomputable def sourceSphereInvertTwoStage (n : ℕ) :
    sourceSphere 0 ⟶ sourceLocalization.obj sphereInvertTwo :=
  sourceStableHomotopyAddEquiv sphereInvertTwo 0
    (loopClass sphereInvertTwo 0 n n (by omega) (sphereCube n))

end KIP126.StableHomotopy.Implementation.Prespectrum
