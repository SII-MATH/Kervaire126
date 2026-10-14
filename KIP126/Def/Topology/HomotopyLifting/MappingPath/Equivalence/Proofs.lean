module

public import KIP126.Def.Topology.HomotopyLifting.MappingPath.Equivalence.Data
public import KIP126.Def.Topology.HomotopyLifting.MappingPath.Proofs
public import KIP126.Def.Topology.HomotopyLifting.Cube.Boundary.Comparison.Proofs
public import KIP126.Def.Topology.Path.Translation.HomotopyGroup.Proofs

@[expose] public section

namespace KIP126.Topology.HomotopyLifting
open scoped unitInterval
universe u v
set_option backward.isDefEq.respectTransparency false

/-- The actual endpoint projection has homotopy-group bijections at
every one of its points whenever the original map does. -/
theorem mappingPathEndpoint_homotopy_bijective
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X,Y)) (n : ℕ)
    (hf : ∀ x, Function.Bijective (continuousHomotopyMap f x (f x) rfl n))
    (z : MappingPathSpace f) :
    Function.Bijective (continuousHomotopyMap (mappingPathEndpoint f) z
      (mappingPathEndpoint f z) rfl n) := by
  have hr := homotopyEquiv_continuousHomotopyMap_bijective (mappingPathSourceHomotopyEquiv f) z n
  have hc := continuousHomotopyMap_comp_bijective (mappingPathSourceProjection f) f z n hr (hf z.val.1)
  let H := mappingPathEndpointHomotopy f
  let e := homotopyBasepointEquiv (homotopyPointPath H z) n
  have heq : e ∘ continuousHomotopyMap (f.comp (mappingPathSourceProjection f)) z
      ((f.comp (mappingPathSourceProjection f)) z) rfl n =
      continuousHomotopyMap (mappingPathEndpoint f) z (mappingPathEndpoint f z) rfl n :=
    funext (continuousHomotopyMap_homotopy H z n)
  rw [← heq]
  exact e.bijective.comp hc

/-- Mapping-path factorization of an actual weak homotopy equivalence
has the full cube-boundary lifting property, proved geometrically. -/
theorem mappingPathEndpoint_hasCubeBoundaryLifting
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X,Y)) (e : X)
    (hf : ∀ x n, Function.Bijective (continuousHomotopyMap f x (f x) rfl n)) :
    HasCubeBoundaryLifting (mappingPathEndpoint f) :=
  (mappingPathEndpoint_hasCubicalLifting f).hasCubeBoundaryLifting_of_homotopy_bijective
    (mappingPathSourceInclusion f e) (fun z n => mappingPathEndpoint_homotopy_bijective f n (fun x => hf x n) z)

end KIP126.Topology.HomotopyLifting
