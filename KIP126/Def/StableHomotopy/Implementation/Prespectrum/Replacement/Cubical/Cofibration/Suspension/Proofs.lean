module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Cofibration.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Lifting.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Adjunction.Data
public import Mathlib.CategoryTheory.LiftingProperties.Adjunction

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory KIP126.Topology.HomotopyLifting
universe u
set_option backward.isDefEq.respectTransparency false

/-- Actual reduced suspension preserves cubical cofibrations, through
the constructed strict suspension-loop adjunction and proved loop lifting. -/
theorem IsCubicalCofibration.suspension {X Y : Prespectrum.{u}}
    {i : X ⟶ Y} (hi : IsCubicalCofibration i) :
    IsCubicalCofibration (suspensionMap i) := by
  intro E B p hp
  apply (suspensionLoopAdjunction.hasLiftingProperty_iff i p).mpr
  exact hi (loopMap p) (loopMap_level_hasCubeBoundaryLifting p hp)

/-- The actual suspension of a spectrum with genuine cubical lifting
again has that property; the lift is its actual uncurried loop lift. -/
theorem IsCubicallyCofibrant.suspension {X : Prespectrum.{u}}
    (hX : IsCubicallyCofibrant X) : IsCubicallyCofibrant X.suspension := by
  intro E B p hp
  constructor
  intro t b sq
  obtain ⟨l,hl⟩ := hX.lift (loopMap p) (loopMap_level_hasCubeBoundaryLifting p hp)
    (suspensionLoopCurry b)
  refine CommSq.HasLift.mk' {
    l := suspensionLoopUncurry l
    fac_left := zeroPrespectrum_isZero.eq_of_src _ _
    fac_right := ?_ }
  apply (suspensionLoopAdjunction.homEquiv X B).injective
  change suspensionLoopCurry (suspensionLoopUncurry l ≫ p) = suspensionLoopCurry b
  rw [suspensionLoopCurry_natural_right, suspensionLoopCurry_uncurry, hl]

end KIP126.StableHomotopy.Implementation.Prespectrum
