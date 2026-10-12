module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cone.Identity.Square.Data

@[expose] public section
namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

@[simp] theorem coneIdentitySquare_zero (X : Prespectrum.{u}) :
    coneIdentitySquare X ≫ pathEvaluation (pathPrespectrum (cone (𝟙 X))) 0 = coneNullPath (𝟙 X) := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  apply ContinuousMap.ext
  intro t
  change Quot.mk (ConeRelation (𝟙 X) n)
    (.inr (x,unitInterval.symm (unitInterval.symm 0 * unitInterval.symm t))) =
    Quot.mk (ConeRelation (𝟙 X) n) (.inr (x,t))
  simp

@[simp] theorem coneIdentitySquare_one (X : Prespectrum.{u}) :
    coneIdentitySquare X ≫ pathEvaluation (pathPrespectrum (cone (𝟙 X))) 1 =
      zeroMap X (pathPrespectrum (cone (𝟙 X))) := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  apply ContinuousMap.ext
  intro t
  change Quot.mk (ConeRelation (𝟙 X) n)
    (.inr (x,unitInterval.symm (unitInterval.symm 1 * unitInterval.symm t))) =
    (coneLevel (𝟙 X) n).point
  simp only [unitInterval.symm_one,zero_mul,unitInterval.symm_zero]
  exact Quot.sound (ConeRelation.finish x)
end KIP126.StableHomotopy.Implementation.Prespectrum
