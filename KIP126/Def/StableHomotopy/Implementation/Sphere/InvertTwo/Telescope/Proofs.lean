module

public import KIP126.Def.StableHomotopy.Implementation.Sphere.InvertTwo.Telescope.Data

@[expose] public section

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
