module

public import KIP126.Def.StableHomotopy.Implementation.Sphere.InvertTwo.Telescope.Representatives.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory

/-- The representative lift descends to every actual stable class of the
original doubled-bond sphere, using its proved homotopy and stabilization
relations. Inverse identities with the telescope comparison are separate
mathematical statements. -/
noncomputable def sourceSphereInvertTwoHomotopyLift (d : ℤ) :
    StableHomotopy sphereInvertTwo d →
      (sourceSphere d ⟶ sourceScalarTelescope 2 (sourceSphere 0)) :=
  Quot.lift sourceSphereInvertTwoRepresentativeLift
    sourceSphereInvertTwoRepresentativeLift_relation

end KIP126.StableHomotopy.Implementation.Prespectrum
