module

public import KIP126.Def.Topology.SmallObject.Cubical.Data
public import KIP126.Def.Topology.SmallObject.Topological.Proofs
public import KIP126.Def.Topology.HomotopyLifting.Cube.Boundary.Topology.Proofs

@[expose] public section

namespace KIP126.Topology.SmallObject

open CategoryTheory CategoryTheory.Limits HomotopyLifting

universe u

set_option backward.isDefEq.respectTransparency false

@[simp] theorem cubicalComparison_point (S : TopCat.{u}) (s : S) :
    cubicalComparison S s (cubicalReplacementPoint S s) = s :=
  ConcreteCategory.congr_hom
    (cellularComparison_stage cubeBoundaryInclusion (pointOver S s) 0) (ULift.up PUnit.unit)

/-- The constructed comparison genuinely fills every full finite cube
boundary problem; the lifting property is proved from its actual stages. -/
theorem cubicalComparison_hasCubeBoundaryLifting (S : TopCat.{u}) (s : S) :
    HasCubeBoundaryLifting (cubicalComparison S s).hom := by
  letI : T1Space (pointOver S s).left :=
    inferInstanceAs (T1Space (ULift.{u} PUnit))
  apply (hasCubeBoundaryLifting_iff_lifting _).mpr
  intro n
  exact cellularComparison_hasLiftingProperty cubeBoundaryInclusion (pointOver S s)
    cubeBoundaryInclusion_isClosedEmbedding n

/-- The actual cubical attachment comparison induces bijections on all
based homotopy sets, with no replacement or approximation assumption. -/
theorem cubicalComparison_homotopy_bijective (S : TopCat.{u}) (s : S) (n : ℕ) :
    Function.Bijective (continuousHomotopyMap (cubicalComparison S s).hom
      (cubicalReplacementPoint S s) s (cubicalComparison_point S s) n) :=
  (cubicalComparison_hasCubeBoundaryLifting S s).continuousHomotopyMap_bijective
    _ _ _ n

end KIP126.Topology.SmallObject
