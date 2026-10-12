module

public import KIP126.Def.StableHomotopy.Implementation.Sphere.InvertTwo.Telescope.Stages.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.ScalarLocalization.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory

/-- The actual map from the scalar-two telescope of S⁰ to the original
doubled-bond sphere, extending its specified finite-stage cube maps. -/
noncomputable def sourceSphereInvertTwoTelescopeComparison :
    sourceScalarTelescope 2 (sourceSphere 0) ⟶ sourceLocalization.obj sphereInvertTwo :=
  (sourceHomotopyColimit_exists_desc (sourceScalarSequence 2 (sourceSphere 0))
    sourceSphereInvertTwoStage (by
      intro n
      rw [sourceScalarSequence_step]
      exact sourceSphereInvertTwoStage_step n)).choose

end KIP126.StableHomotopy.Implementation.Prespectrum
