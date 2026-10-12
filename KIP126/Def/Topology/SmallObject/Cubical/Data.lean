module

public import KIP126.Def.Topology.SmallObject.Sequence.Data
public import KIP126.Def.Topology.HomotopyLifting.Cube.Boundary.Data
public import Mathlib.Topology.Category.TopCat.Limits.Basic

@[expose] public section

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
