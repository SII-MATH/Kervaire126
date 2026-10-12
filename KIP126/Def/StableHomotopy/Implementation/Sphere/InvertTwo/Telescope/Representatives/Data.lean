module

public import KIP126.Def.StableHomotopy.Implementation.Sphere.InvertTwo.Telescope.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory

/-- Send an actual doubled-bond representative to the corresponding
ordinary sphere class at the same finite stage of the scalar telescope. -/
noncomputable def sourceSphereInvertTwoRepresentativeLift {d : ℤ}
    (a : Representative sphereInvertTwo d) :
    sourceSphere d ⟶ sourceScalarTelescope 2 (sourceSphere 0) :=
  sourceStableHomotopyAddEquiv sphere d
    (loopClass sphere d a.stage a.dimension a.degree a.loop) ≫
    (eqToIso sourceSphere_zero).inv ≫
      sourceHomotopyColimitInclusion (sourceScalarSequence 2 (sourceSphere 0)) a.stage

end KIP126.StableHomotopy.Implementation.Prespectrum
