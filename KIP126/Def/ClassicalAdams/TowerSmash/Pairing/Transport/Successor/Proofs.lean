import KIP126.Def.ClassicalAdams.TowerSmash.Pairing.Transport.Proofs

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H)
  [∀ Y : C, (tensorRight Y).CommShift ℤ]
  [∀ Y : C, (tensorRight Y).IsTriangulated]

/-- The actual tower pairing at a successor is tensoring the preceding
pairing by the unit fiber, through the existing fiber comparisons. -/
theorem adamsTowerSpherePairingIso_succ_comparison (s t : ℕ) :
    (adamsTowerSpherePairingIso unit (s + 1) t).hom ≫
        (adamsFiberTensorIso unit (adamsTower unit (𝟙_ C) (t + s))).hom =
      ((adamsFiberTensorIso unit (adamsTower unit (𝟙_ C) s)).hom ▷
        adamsTower unit (𝟙_ C) t) ≫
        (α_ (fiber unit) (adamsTower unit (𝟙_ C) s)
          (adamsTower unit (𝟙_ C) t)).hom ≫
        fiber unit ◁ (adamsTowerSpherePairingIso unit s t).hom := by
  have hs (k : ℕ) :
      (adamsFiberTensorIso unit (adamsTower unit (𝟙_ C) k)).hom ≫
          fiber unit ◁ (adamsTowerSmashIso unit (𝟙_ C) k).hom =
        (adamsTowerSmashIso unit (𝟙_ C) (k + 1)).hom := rfl
  apply (cancel_mono
    (fiber unit ◁ (adamsTowerSmashIso unit (𝟙_ C) (t + s)).hom)).mp
  have hc := adamsTowerSpherePairingIso_comparison unit (s + 1) t
  simp only [Nat.add_succ, Nat.add_zero] at hc
  erw [Category.assoc, hs, hc]
  rw [adamsSmashSpherePairingIso_succ]
  change (((adamsFiberTensorIso unit (adamsTower unit (𝟙_ C) s)).hom ≫
      fiber unit ◁ (adamsTowerSmashIso unit (𝟙_ C) s).hom) ⊗ₘ
      (adamsTowerSmashIso unit (𝟙_ C) t).hom) ≫
      (α_ (fiber unit) (adamsSmashTower unit (𝟙_ C) s)
        (adamsSmashTower unit (𝟙_ C) t)).hom ≫
      fiber unit ◁ (adamsSmashSpherePairingIso unit s t).hom =
    (((adamsFiberTensorIso unit (adamsTower unit (𝟙_ C) s)).hom ▷
      adamsTower unit (𝟙_ C) t) ≫
      (α_ (fiber unit) (adamsTower unit (𝟙_ C) s)
        (adamsTower unit (𝟙_ C) t)).hom ≫
      fiber unit ◁ (adamsTowerSpherePairingIso unit s t).hom) ≫
      fiber unit ◁ (adamsTowerSmashIso unit (𝟙_ C) (t + s)).hom
  simp only [Category.assoc, ← whiskerLeft_comp]
  rw [adamsTowerSpherePairingIso_comparison]
  simp only [whiskerLeft_comp, tensorHom_def, Category.assoc,
    comp_whiskerRight]
  simp only [associator_naturality_middle_assoc, associator_naturality_right_assoc]

end
end KIP126.Classical.Adams
