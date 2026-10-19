module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Cube.Boundary.HomotopyExtension.Proofs
public import KIP126.Def.Topology.HomotopyLifting.Cube.Boundary.Product.Proofs

@[expose] public section

namespace KIP126.Topology.HomotopyLifting
open CategoryTheory _root_.Topology
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

/-- Retain the endpoint coordinate while retracting the actual cube cylinder. -/
theorem cubeBoundaryProductTop_hasHomotopyExtension (n : ℕ) :
    HomotopyExtension.HasHomotopyExtension (cubeBoundaryProductTop.{u} n) := by
  obtain ⟨r,h0,hi,hr⟩ :=
    (cubeBoundaryInclusion_hasHomotopyExtension.{u} n).exists_cylinder_retraction
  let r' : C(cubeBoundaryProductEnds.{u} n × I,cubeBoundaryProductEnds.{u} n × I) :=
    ⟨fun q => ((q.1.1,(r (q.1.2,q.2)).1),(r (q.1.2,q.2)).2),
      (continuous_fst.fst.prodMk
        (r.continuous.comp (continuous_fst.snd.prodMk continuous_snd)).fst).prodMk
        (r.continuous.comp (continuous_fst.snd.prodMk continuous_snd)).snd⟩
  have he : IsClosedEmbedding (cubeBoundaryProductTop.{u} n) :=
    IsClosedEmbedding.id.prodMap (cubeBoundaryInclusion_isClosedEmbedding n)
  apply HomotopyExtension.hasHomotopyExtension_of_cylinder_retraction _ he r'
  · intro b
    change ((b.1,(r (b.2,0)).1),(r (b.2,0)).2) = (b,0)
    rw [h0]
    rfl
  · intro a t
    change ((a.1,(r (cubeBoundaryInclusion n a.2,t)).1),
      (r (cubeBoundaryInclusion n a.2,t)).2) = ((a.1,cubeBoundaryInclusion n a.2),t)
    rw [hi]
  · intro q
    rcases hr (q.1.2,q.2) with h | ⟨a,ha⟩
    · exact Or.inl h
    · exact Or.inr ⟨(q.1.1,a),Prod.ext rfl ha⟩

end KIP126.Topology.HomotopyLifting

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory _root_.Topology KIP126.Topology.HomotopyLifting
set_option backward.isDefEq.respectTransparency false

/-- The actual top leg of the cube-boundary parameter pushout has based
homotopy extension after tensoring with any original prespectrum. -/
theorem spaceSmashCubeBoundaryProductTop_level_hasBasedHomotopyExtension
    (n : ℕ) (X : Prespectrum.{0}) (k : ℕ) :
    BasedSpace.HasBasedHomotopyExtension ((evaluationFunctor k).map
      (spaceSmashMap (BasedSpace.adjoinPointMap (cubeBoundaryProductTop n)) (𝟙 X))) := by
  have he : IsClosedEmbedding (cubeBoundaryProductTop.{0} n) :=
    IsClosedEmbedding.id.prodMap (cubeBoundaryInclusion_isClosedEmbedding n)
  apply BasedSpace.smashMap_hasBasedHomotopyExtension
    (BasedSpace.adjoinPointMap (cubeBoundaryProductTop n))
  · apply IsClosedEmbedding.isClosedEmbedding_iff_continuous_injective_isClosedMap.mpr
    refine ⟨(BasedSpace.adjoinPointMap (cubeBoundaryProductTop n)).map.continuous,
      BasedSpace.adjoinPointMap_injective _ he.injective,?_⟩
    exact he.isClosedMap.sumMap (fun s hs => by simpa only [Set.image_id] using hs)
  · exact BasedSpace.adjoinPointMap_hasHomotopyExtension _
      (cubeBoundaryProductTop_hasHomotopyExtension n)

end KIP126.StableHomotopy.Implementation.Prespectrum
