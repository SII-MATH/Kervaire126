import KIP126.Def.ClassicalAdams.TowerSmash.Pairing.Right.Predicates

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H)

/-- A single two-factor compatibility propagates after tensoring with any X. -/
theorem unitFiberInclusionCommutes_tensor (h : UnitFiberInclusionCommutes unit) (X : C) :
    (fiberι unit ▷ (fiber unit ⊗ X)) ≫ (λ_ (fiber unit ⊗ X)).hom =
      fiber unit ◁ ((fiberι unit ▷ X) ≫ (λ_ X).hom) := by
  apply (cancel_epi (α_ (fiber unit) (fiber unit) X).hom).mp
  simp only [whiskerLeft_comp]
  rw [← associator_naturality_left_assoc, leftUnitor_tensor_hom]
  simp only [Iso.hom_inv_id_assoc]
  rw [← associator_naturality_middle_assoc, MonoidalCategory.triangle]
  simp only [← comp_whiskerRight]
  exact congrArg (fun f => f ▷ X) h

/-- Consecutive smash-tower transitions commute past the outer fiber factor
under the explicit two-factor condition. -/
theorem adamsSmashTowerStep_succ_of_inclusion_commutes
    (h : UnitFiberInclusionCommutes unit) (X : C) (s : ℕ) :
    adamsSmashTowerStep unit X (s + 1) = fiber unit ◁ adamsSmashTowerStep unit X s :=
  unitFiberInclusionCommutes_tensor unit h (adamsSmashTower unit X s)

private theorem smashTower_eqToHom_succ (a b : ℕ) (h : a = b) :
    eqToHom (congrArg (adamsSmashTower unit (𝟙_ C)) (congrArg Nat.succ h)) =
      fiber unit ◁ eqToHom (congrArg (adamsSmashTower unit (𝟙_ C)) h) := by
  subst b
  simp only [eqToHom_refl, whiskerLeft_id]
  rfl

theorem adamsSmashSpherePairingNextRight_zero (t : ℕ) :
    adamsSmashSpherePairingNextRight unit 0 t =
      (λ_ (adamsSmashTower unit (𝟙_ C) (t + 1))).hom := by
  simp only [adamsSmashSpherePairingNextRight, adamsSmashSpherePairingIso_zero,
    eqToHom_refl, Category.comp_id]

theorem adamsSmashSpherePairingNextRight_succ (s t : ℕ) :
    adamsSmashSpherePairingNextRight unit (s + 1) t =
      (α_ (fiber unit) (adamsSmashTower unit (𝟙_ C) s)
        (adamsSmashTower unit (𝟙_ C) (t + 1))).hom ≫
        (fiber unit ◁ adamsSmashSpherePairingNextRight unit s t) := by
  unfold adamsSmashSpherePairingNextRight
  rw [adamsSmashSpherePairingIso_succ]
  erw [Category.assoc, smashTower_eqToHom_succ unit ((t + 1) + s) (t + s + 1)
    (Nat.succ_add t s), whiskerLeft_comp]
  simp only [adamsSmashSpherePairingIso, Iso.trans_hom, whiskerLeft_comp,
    Category.assoc]
  exact congrArg (fun f =>
    (α_ (fiber unit) (adamsSmashTower unit (𝟙_ C) s)
      (adamsSmashTower unit (𝟙_ C) (t + 1))).hom ≫ f) (Category.assoc _ _ _)

/-- Under the concrete two-factor condition, concatenation commutes with
the second input's successor map at every pair of stages. This remains a
homotopy-category equality, not a coherent tower pairing or Leibniz witness. -/
theorem adamsSmashSpherePairingIso_step_right
    (h : UnitFiberInclusionCommutes unit) (s t : ℕ) :
    adamsSmashSpherePairingNextRight unit s t ≫
        adamsSmashTowerStep unit (𝟙_ C) (t + s) =
      (adamsSmashTower unit (𝟙_ C) s ◁ adamsSmashTowerStep unit (𝟙_ C) t) ≫
        (adamsSmashSpherePairingIso unit s t).hom := by
  induction s with
  | zero =>
      rw [adamsSmashSpherePairingNextRight_zero, adamsSmashSpherePairingIso_zero]
      exact (leftUnitor_naturality (adamsSmashTowerStep unit (𝟙_ C) t)).symm
  | succ s ih =>
      rw [adamsSmashSpherePairingNextRight_succ, adamsSmashSpherePairingIso_succ]
      change ((α_ (fiber unit) (adamsSmashTower unit (𝟙_ C) s)
          (adamsSmashTower unit (𝟙_ C) (t + 1))).hom ≫
          fiber unit ◁ adamsSmashSpherePairingNextRight unit s t) ≫
          adamsSmashTowerStep unit (𝟙_ C) ((t + s) + 1) =
        ((fiber unit ⊗ adamsSmashTower unit (𝟙_ C) s) ◁
          adamsSmashTowerStep unit (𝟙_ C) t) ≫
          (α_ (fiber unit) (adamsSmashTower unit (𝟙_ C) s)
            (adamsSmashTower unit (𝟙_ C) t)).hom ≫
            fiber unit ◁ (adamsSmashSpherePairingIso unit s t).hom
      rw [adamsSmashTowerStep_succ_of_inclusion_commutes unit h, Category.assoc]
      erw [← whiskerLeft_comp, ih, whiskerLeft_comp,
        ← associator_naturality_right_assoc]
      rfl

end
end KIP126.Classical.Adams
