module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cone.Iteration.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

@[reassoc] theorem coneIterationComparison_inclusion {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    coneInclusion (coneInclusion f) ≫ coneIterationComparison f = coneBoundary f := rfl

theorem coneIterationSquare_zero {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    coneIterationSquare f ≫ pathEvaluation (pathPrespectrum (cone (coneInclusion f))) 0 =
      f ≫ coneNullPath (coneInclusion f) := by
  apply Hom.ext; funext n
  apply ContinuousMap.ext; intro x
  apply ContinuousMap.ext; intro t
  exact coneIterationLoop_parameter_zero_left f n x t

theorem coneIterationSquare_one {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    coneIterationSquare f ≫ pathEvaluation (pathPrespectrum (cone (coneInclusion f))) 1 =
      zeroMap X (pathPrespectrum (cone (coneInclusion f))) := by
  apply Hom.ext; funext n
  apply ContinuousMap.ext; intro x
  apply ContinuousMap.ext; intro t
  change (coneIterationLoop f).level n x (coneIterationParameter 1 t) = _
  rw [coneIterationParameter_one_left, Path.target]
  rfl

theorem coneIterationOuterSquare_zero {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    coneIterationOuterSquare f ≫ pathEvaluation (pathPrespectrum (cone (coneInclusion f))) 0 =
      coneNullPath (coneInclusion f) := by
  apply Hom.ext; funext n
  apply ContinuousMap.ext; intro y
  apply ContinuousMap.ext; intro t
  change Quot.mk (ConeRelation (coneInclusion f) n)
    (.inr (y,unitInterval.symm (unitInterval.symm 0 * unitInterval.symm t))) =
      Quot.mk (ConeRelation (coneInclusion f) n) (.inr (y,t))
  simp

theorem coneIterationOuterSquare_one {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    coneIterationOuterSquare f ≫ pathEvaluation (pathPrespectrum (cone (coneInclusion f))) 1 =
      zeroMap Y (pathPrespectrum (cone (coneInclusion f))) := by
  apply Hom.ext; funext n
  apply ContinuousMap.ext; intro y
  apply ContinuousMap.ext; intro t
  change Quot.mk (ConeRelation (coneInclusion f) n)
    (.inr (y,unitInterval.symm (unitInterval.symm 1 * unitInterval.symm t))) = _
  simp only [unitInterval.symm_one, zero_mul, unitInterval.symm_zero]
  exact Quot.sound (ConeRelation.finish y)

end KIP126.StableHomotopy.Implementation.Prespectrum
