module

public import KIP126.Def.Topology.SmallObject.Sequence.Data
public import KIP126.Def.Topology.HomotopyLifting.Cube.Boundary.Data
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import KIP126.Def.Topology.SmallObject.Topological.Proofs
public import KIP126.Def.Topology.HomotopyLifting.Cube.Boundary.Topology.Proofs

@[expose] public section

section

namespace KIP126.Topology.SmallObject

open CategoryTheory CategoryTheory.Limits HomotopyLifting

universe u

/-- The specified initial point over the target, before any attachment. -/
def pointOver (S : TopCat.{u}) (s : S) : Over S :=
  Over.mk (TopCat.ofHom (ContinuousMap.const (ULift.{u} PUnit) s))

/-- The actual countable attachment of all finite cube-boundary lifting
problems, beginning at the specified target point. -/
noncomputable abbrev cubicalReplacement (S : TopCat.{u}) (s : S) : TopCat.{u} :=
  cellularReplacement cubeBoundaryInclusion (pointOver S s)

/-- The actual target comparison from the countable cubical attachment. -/
noncomputable def cubicalComparison (S : TopCat.{u}) (s : S) :
    cubicalReplacement S s ⟶ S :=
  cellularComparison cubeBoundaryInclusion (pointOver S s)

/-- The point inherited from the genuine initial point inclusion. -/
noncomputable def cubicalReplacementPoint (S : TopCat.{u}) (s : S) : cubicalReplacement S s :=
  colimit.ι (cellularSequence cubeBoundaryInclusion (pointOver S s)) 0 (ULift.up PUnit.unit)

end KIP126.Topology.SmallObject

end

section

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

end
