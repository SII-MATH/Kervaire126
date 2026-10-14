module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Cofibration.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cone.Universal.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u
set_option backward.isDefEq.respectTransparency false

/-- The literal cone inclusion is an actual cubical cofibration whenever
its attached source has the proved object lifting property. Its entire
nullhomotopy lifts with both endpoints fixed. -/
theorem coneInclusion_isCubicalCofibration {X Y : Prespectrum.{u}}
    (hX : IsCubicallyCofibrant X) (f : X ⟶ Y) :
    IsCubicalCofibration (coneInclusion f) := by
  intro E B p hp
  constructor
  intro a b sq
  let H : StrictHomotopy ((f ≫ a) ≫ p) ((zeroMap X E) ≫ p) := {
    hom := coneNullPath f ≫ pathMap b
    zero := by
      rw [Category.assoc, pathMap_evaluation, ← Category.assoc, coneNullPath_zero,
        Category.assoc, ← sq.w, Category.assoc]
    one := by
      rw [Category.assoc, pathMap_evaluation, ← Category.assoc, coneNullPath_one]
      apply Hom.ext
      funext n
      apply ContinuousMap.ext
      intro x
      exact (b.point n).trans (p.point n).symm }
  obtain ⟨G,hG⟩ := hX.lift_strictHomotopy p hp H
  refine CommSq.HasLift.mk' {
    l := coneLift f a G.hom G.zero G.one
    fac_left := coneInclusion_lift f a G.hom G.zero G.one
    fac_right := ?_ }
  apply coneHom_ext f
  · rw [← Category.assoc, coneInclusion_lift]
    exact sq.w
  · rw [pathMap_comp, ← Category.assoc, coneNullPath_lift]
    exact hG

end KIP126.StableHomotopy.Implementation.Prespectrum
