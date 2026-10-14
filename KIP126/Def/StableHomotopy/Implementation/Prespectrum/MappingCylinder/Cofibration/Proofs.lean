module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingCylinder.Universal.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Cofibration.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u
set_option backward.isDefEq.respectTransparency false

/-- Including the target into the original mapping cylinder has the
actual cubical lifting property whenever the attached source does. -/
theorem mappingCylinderSection_isCubicalCofibration {X Y : Prespectrum.{u}}
    (hX : IsCubicallyCofibrant X) (f : X ⟶ Y) :
    IsCubicalCofibration (mappingCylinderSection f) := by
  intro E B p hp
  constructor
  intro a b sq
  obtain ⟨c,hc⟩ := hX.lift p hp (mappingCylinderInclusion f ≫ b)
  let H : StrictHomotopy (c ≫ p) ((f ≫ a) ≫ p) := {
    hom := mappingCylinderPath f ≫ pathMap b
    zero := by
      rw [Category.assoc,pathMap_evaluation,← Category.assoc,mappingCylinderPath_zero]
      exact hc.symm
    one := by
      rw [Category.assoc,pathMap_evaluation,← Category.assoc,mappingCylinderPath_one,
        Category.assoc,← sq.w,← Category.assoc] }
  obtain ⟨G,hG⟩ := hX.lift_strictHomotopy p hp H
  refine CommSq.HasLift.mk' {
    l := mappingCylinderDesc f a G.hom G.one
    fac_left := mappingCylinderSection_desc f a G.hom G.one
    fac_right := ?_ }
  apply mappingCylinderHom_ext f
  · rw [← Category.assoc,mappingCylinderSection_desc]
    exact sq.w
  · rw [pathMap_comp,← Category.assoc,mappingCylinderPath_desc]
    exact hG

/-- The original reduced mapping cylinder retains actual cofibrancy
of both inputs, by its proved target inclusion. -/
theorem IsCubicallyCofibrant.mappingCylinder {X Y : Prespectrum.{u}}
    (hX : IsCubicallyCofibrant X) (hY : IsCubicallyCofibrant Y) (f : X ⟶ Y) :
    IsCubicallyCofibrant (mappingCylinder f) := by
  intro E B p hp
  exact IsCubicallyCofibrant.of_cubicalCofibration hY
    (mappingCylinderSection_isCubicalCofibration hX f) p hp

/-- The free-end inclusion of the actual mapping cylinder is a cubical
cofibration. Prescribed endpoint lifts and the entire actual path are
retained, so this is a strict lifting statement. -/
theorem mappingCylinderInclusion_isCubicalCofibration {X Y : Prespectrum.{u}}
    (hX : IsCubicallyCofibrant X) (hY : IsCubicallyCofibrant Y) (f : X ⟶ Y) :
    IsCubicalCofibration (mappingCylinderInclusion f) := by
  intro E B p hp
  constructor
  intro a b sq
  obtain ⟨c,hc⟩ := hY.lift p hp (mappingCylinderSection f ≫ b)
  let H : StrictHomotopy (a ≫ p) ((f ≫ c) ≫ p) := {
    hom := mappingCylinderPath f ≫ pathMap b
    zero := by
      rw [Category.assoc,pathMap_evaluation,← Category.assoc,mappingCylinderPath_zero]
      exact sq.w.symm
    one := by
      rw [Category.assoc,pathMap_evaluation,← Category.assoc,mappingCylinderPath_one,
        Category.assoc,← hc,← Category.assoc] }
  obtain ⟨G,hG⟩ := hX.lift_strictHomotopy p hp H
  refine CommSq.HasLift.mk' {
    l := mappingCylinderDesc f c G.hom G.one
    fac_left := by rw [mappingCylinderInclusion_desc]; exact G.zero
    fac_right := ?_ }
  apply mappingCylinderHom_ext f
  · rw [← Category.assoc,mappingCylinderSection_desc]
    exact hc
  · rw [pathMap_comp,← Category.assoc,mappingCylinderPath_desc]
    exact hG

end KIP126.StableHomotopy.Implementation.Prespectrum
