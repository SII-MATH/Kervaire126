module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cone.Iteration.Homotopy.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Group.Laws.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Adjunction.Homotopy.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

/-- Under the actual Puppe collapse, the outer half of the retained
loop is constant and the inner half is the ordinary suspension loop. -/
theorem coneIterationLoop_comparison {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    coneIterationLoop f ≫ loopMap (coneIterationComparison f) =
      loopAdd (zeroMap X (loop X.suspension)) (suspensionLoopCurry (𝟙 X.suspension)) := by
  apply Hom.ext; funext n
  apply ContinuousMap.ext; intro x
  apply Path.ext; funext s
  change (coneIterationComparison f).level n ((coneIterationLoop f).level n x s) =
    ((Path.refl (X.suspension.level n).point).trans
      ((suspensionLoopCurry (𝟙 X.suspension)).level n x)) s
  rw [coneIterationLoop_apply, Path.trans_apply]
  split_ifs <;> rfl

end KIP126.StableHomotopy.Implementation.Prespectrum
