module

public import KIP126.Def.StableHomotopy.Implementation.Sphere.InvertTwo.Telescope.Stages
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.ScalarLocalization.Proofs

@[expose] public section

section

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

end

section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory

/-- Every original telescope stage maps to its specified cube in the
unchanged doubled-bond sphere. -/
theorem sourceSphereInvertTwoTelescopeComparison_stage (n : ℕ) :
    sourceHomotopyColimitInclusion (sourceScalarSequence 2 (sourceSphere 0)) n ≫
      sourceSphereInvertTwoTelescopeComparison = sourceSphereInvertTwoStage n :=
  (sourceHomotopyColimit_exists_desc (sourceScalarSequence 2 (sourceSphere 0))
    sourceSphereInvertTwoStage (by
      intro k
      rw [sourceScalarSequence_step]
      exact sourceSphereInvertTwoStage_step k)).choose_spec n

end KIP126.StableHomotopy.Implementation.Prespectrum

end
