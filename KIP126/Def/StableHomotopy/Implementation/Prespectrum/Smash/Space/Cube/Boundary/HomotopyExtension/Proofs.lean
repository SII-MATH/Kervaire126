module

public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.HomotopyExtension.Based.Smash.Proofs
public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.HomotopyExtension.AdjoinPoint.Proofs
public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.AdjoinPoint.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Cube.Boundary.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Tail.Data
public import KIP126.Def.Topology.HomotopyLifting.Cube.Boundary.Extension.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory _root_.Topology
open KIP126.Topology.HomotopyLifting

/-- The original full cube-boundary tensor has based homotopy extension
at every level for every original prespectrum, including dimension zero. -/
theorem spaceSmashCubeBoundaryMap_level_hasBasedHomotopyExtension
    (n : ℕ) (X : Prespectrum.{0}) (k : ℕ) :
    BasedSpace.HasBasedHomotopyExtension
      ((evaluationFunctor k).map (spaceSmashCubeBoundaryMap n X)) := by
  apply BasedSpace.smashMap_hasBasedHomotopyExtension
    (BasedSpace.adjoinPointMap (cubeBoundaryInclusion n))
  · apply IsClosedEmbedding.isClosedEmbedding_iff_continuous_injective_isClosedMap.mpr
    refine ⟨(BasedSpace.adjoinPointMap (cubeBoundaryInclusion n)).map.continuous,
      BasedSpace.adjoinPointMap_injective _ (cubeBoundaryInclusion_isClosedEmbedding n).injective,?_⟩
    exact (cubeBoundaryInclusion_isClosedEmbedding n).isClosedMap.sumMap
      (fun s hs => by simpa only [Set.image_id] using hs)
  · exact BasedSpace.adjoinPointMap_hasHomotopyExtension _
      (cubeBoundaryInclusion_hasHomotopyExtension n)

end KIP126.StableHomotopy.Implementation.Prespectrum
