module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cone.Iteration.Homotopy

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
universe u
set_option backward.isDefEq.respectTransparency false

/-- Removing the constant half of the actual suspension loop proves the
other strict homotopy-inverse identity for the Puppe comparison. -/
noncomputable def coneIterationInverseHomotopy {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    StrictHomotopy (coneIterationInverse f ≫ coneIterationComparison f) (𝟙 X.suspension) := by
  let c := suspensionLoopCurry (𝟙 X.suspension)
  let H : StrictHomotopy (loopAdd (zeroMap X (loop X.suspension)) c) c := {
    hom := loopLeftUnitPath c
    zero := loopLeftUnitPath_zero c
    one := loopLeftUnitPath_one c }
  have e : suspensionLoopCurry (coneIterationInverse f ≫ coneIterationComparison f) =
      loopAdd (zeroMap X (loop X.suspension)) c := by
    rw [suspensionLoopCurry_natural_right]
    change suspensionLoopCurry (suspensionLoopUncurry (coneIterationLoop f)) ≫ _ = _
    rw [suspensionLoopCurry_uncurry]
    exact coneIterationLoop_comparison f
  have h := H.suspensionUncurry
  rw [← e, suspensionLoopUncurry_curry] at h
  simpa only [c, suspensionLoopUncurry_curry] using h

end KIP126.StableHomotopy.Implementation.Prespectrum
