import KIP126.Def.ClassicalAdams.TowerSmash.Pairing.Right.Transport.Data

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H)
  [∀ Y : C, (tensorRight Y).CommShift ℤ]
  [∀ Y : C, (tensorRight Y).IsTriangulated]

/-- Reindexing respects the existing comparison of the actual and smash towers. -/
theorem adamsTowerSpherePairingNextRight_comparison (s t : ℕ) :
    adamsTowerSpherePairingNextRight unit s t ≫
        (adamsTowerSmashIso unit (𝟙_ C) (t + s + 1)).hom =
      ((adamsTowerSmashIso unit (𝟙_ C) s).hom ⊗ₘ
        (adamsTowerSmashIso unit (𝟙_ C) (t + 1)).hom) ≫
        adamsSmashSpherePairingNextRight unit s t := by
  unfold adamsTowerSpherePairingNextRight adamsSmashSpherePairingNextRight
  rw [Category.assoc,
    ← eqToHom_iso_hom_naturality (adamsTowerSmashIso unit (𝟙_ C)) (Nat.succ_add t s),
    ← Category.assoc, adamsTowerSpherePairingIso_comparison, Category.assoc]

variable [MonoidalPreadditive C]

/-- The right-input transition law on the existing sphere tower, conditional
on the explicit two-factor unit-fiber condition. Neither a witness of that
condition nor coherent multiplicativity or Leibniz is asserted here. -/
theorem adamsTowerSpherePairingIso_step_right
    (h : UnitFiberInclusionCommutes unit) (s t : ℕ) :
    adamsTowerSpherePairingNextRight unit s t ≫
        adamsTowerStep unit (𝟙_ C) (t + s) =
      (adamsTower unit (𝟙_ C) s ◁ adamsTowerStep unit (𝟙_ C) t) ≫
        (adamsTowerSpherePairingIso unit s t).hom := by
  have htensor :
      ((adamsTowerSmashIso unit (𝟙_ C) s).hom ⊗ₘ
          (adamsTowerSmashIso unit (𝟙_ C) (t + 1)).hom) ≫
          (adamsSmashTower unit (𝟙_ C) s ◁ adamsSmashTowerStep unit (𝟙_ C) t) =
        (adamsTower unit (𝟙_ C) s ◁ adamsTowerStep unit (𝟙_ C) t) ≫
          ((adamsTowerSmashIso unit (𝟙_ C) s).hom ⊗ₘ
            (adamsTowerSmashIso unit (𝟙_ C) t).hom) := by
    simp only [← id_tensorHom, tensorHom_comp_tensorHom, Category.comp_id,
      Category.id_comp, adamsTowerSmashIso_step]
  apply (cancel_mono (adamsTowerSmashIso unit (𝟙_ C) (t + s)).hom).mp
  simp only [Category.assoc, ← adamsTowerSmashIso_step]
  rw [← Category.assoc, adamsTowerSpherePairingNextRight_comparison]
  simp only [Category.assoc]
  rw [adamsSmashSpherePairingIso_step_right unit h]
  rw [← Category.assoc, htensor, Category.assoc, ← adamsTowerSpherePairingIso_comparison]

end
end KIP126.Classical.Adams
