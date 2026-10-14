module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingCylinder.Endpoint.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingCylinder.Cofibration.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Limits
universe u
set_option backward.isDefEq.respectTransparency false

/-- The simultaneous endpoint inclusion has actual cubical lifting,
retaining both prescribed lifts and the full intervening path. -/
theorem cylinderEndpoints_isCubicalCofibration {X : Prespectrum.{u}}
    (hX : IsCubicallyCofibrant X) : IsCubicalCofibration (cylinderEndpoints X) := by
  intro E B p hp
  constructor
  intro a b sq
  let a₀ : X ⟶ E := coprod.inl ≫ a
  let a₁ : X ⟶ E := coprod.inr ≫ a
  have h₀ : a₀ ≫ p = mappingCylinderInclusion (𝟙 X) ≫ b := by
    rw [show a₀ = coprod.inl ≫ a from rfl,Category.assoc,sq.w,← Category.assoc]
    exact congrArg (fun k => k ≫ b) (coprod.inl_desc _ _)
  have h₁ : a₁ ≫ p = mappingCylinderSection (𝟙 X) ≫ b := by
    rw [show a₁ = coprod.inr ≫ a from rfl,Category.assoc,sq.w,← Category.assoc]
    exact congrArg (fun k => k ≫ b) (coprod.inr_desc _ _)
  let H : StrictHomotopy (a₀ ≫ p) (a₁ ≫ p) := {
    hom := mappingCylinderPath (𝟙 X) ≫ pathMap b
    zero := by rw [Category.assoc,pathMap_evaluation,← Category.assoc,mappingCylinderPath_zero,h₀]
    one := by rw [Category.assoc,pathMap_evaluation,← Category.assoc,mappingCylinderPath_one,
      Category.id_comp,h₁] }
  obtain ⟨G,hG⟩ := hX.lift_strictHomotopy p hp H
  have G₁ : G.hom ≫ pathEvaluation E 1 = 𝟙 X ≫ a₁ := by simpa using G.one
  refine CommSq.HasLift.mk' {
    l := mappingCylinderDesc (𝟙 X) a₁ G.hom G₁
    fac_left := ?_
    fac_right := ?_ }
  · apply coprod.hom_ext
    · change coprod.inl ≫ coprod.desc _ _ ≫ _ = _
      rw [coprod.inl_desc_assoc,mappingCylinderInclusion_desc]
      exact G.zero
    · change coprod.inr ≫ coprod.desc _ _ ≫ _ = _
      rw [coprod.inr_desc_assoc,mappingCylinderSection_desc]
  · apply mappingCylinderHom_ext (𝟙 X)
    · rw [← Category.assoc,mappingCylinderSection_desc]
      exact h₁
    · rw [pathMap_comp,← Category.assoc,mappingCylinderPath_desc]
      exact hG

end KIP126.StableHomotopy.Implementation.Prespectrum
