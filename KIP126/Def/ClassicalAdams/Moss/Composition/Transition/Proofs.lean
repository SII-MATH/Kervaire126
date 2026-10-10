import KIP126.Def.ClassicalAdams.Moss.Composition.Proofs
import KIP126.Def.ClassicalAdams.TowerSmash.Proofs
import KIP126.Def.ClassicalAdams.TowerSmash.Pairing.Right.Proofs

namespace KIP126.Classical.Adams.Moss

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
universe u v
set_option backward.isDefEq.respectTransparency false
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [MonoidalClosed C] [BraidedCategory C]
  {H : C} (unit : 𝟙_ C ⟶ H)

omit [MonoidalClosed C] [BraidedCategory C] in
/-- Splitting off the mapping object respects removal of a unit-fiber factor. -/
theorem smashSphereTensorIso_step (A : C) (s : ℕ) :
    (adamsSmashSphereTensorIso unit A (s + 1)).hom ≫ adamsSmashTowerStep unit A s =
      (adamsSmashTowerStep unit (𝟙_ C) s ▷ A) ≫
        (adamsSmashSphereTensorIso unit A s).hom := by
  change ((α_ (fiber unit) (adamsSmashTower unit (𝟙_ C) s) A).hom ≫
      fiber unit ◁ (adamsSmashSphereTensorIso unit A s).hom) ≫
        ((fiberι unit ▷ adamsSmashTower unit A s) ≫ (λ_ _).hom) =
      (((fiberι unit ▷ adamsSmashTower unit (𝟙_ C) s) ≫ (λ_ _).hom) ▷ A) ≫ _
  simp only [Category.assoc]
  rw [whisker_exchange_assoc, leftUnitor_naturality]
  rw [← associator_naturality_left_assoc, leftUnitor_tensor_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, comp_whiskerRight]

/-- In the actual sphere-factor coordinates, composition uses exactly the
existing sphere concatenation and the selected internal composition. -/
theorem smashComposition_coordinates (X Y Z : C) (s t : ℕ) :
    ((adamsSmashSphereTensorIso unit (mappingObject X Y) s).hom ⊗ₘ
        (adamsSmashSphereTensorIso unit (mappingObject Y Z) t).hom) ≫
        smashComposition unit X Y Z s t =
      tensorμ (adamsSmashTower unit (𝟙_ C) s) (mappingObject X Y)
        (adamsSmashTower unit (𝟙_ C) t) (mappingObject Y Z) ≫
        ((adamsSmashSpherePairingIso unit s t).hom ⊗ₘ Mapping.composition X Y Z) ≫
        (adamsSmashSphereTensorIso unit (mappingObject X Z) (t + s)).hom := by
  simp only [smashComposition, ← Category.assoc]
  rw [tensorHom_comp_tensorHom]
  simp only [Iso.hom_inv_id, id_tensorHom_id, Category.id_comp]

omit [HasFunctorialCofiber (C := C)] [MonoidalClosed C] in
private theorem shuffle_pairing_naturality {A A' B B' D D' U V W : C}
    (a : A ⟶ A') (b : B ⟶ B') (d : D ⟶ D')
    (f : A ⊗ B ⟶ D) (g : A' ⊗ B' ⟶ D') (c : U ⊗ V ⟶ W)
    (h : f ≫ d = (a ⊗ₘ b) ≫ g) :
    ((a ▷ U) ⊗ₘ (b ▷ V)) ≫ tensorμ A' U B' V ≫ (g ⊗ₘ c) =
      tensorμ A U B V ≫ (f ⊗ₘ c) ≫ (d ▷ W) := by
  simp only [← tensorHom_id]
  rw [tensorμ_natural_assoc]
  simp only [tensorHom_comp_tensorHom, id_tensorHom_id,
    Category.id_comp, Category.comp_id, ← h]

/-- The concrete mapping smash composition respects the first input's
successor at every pair of stages, without a connectivity hypothesis. -/
theorem smashComposition_step_left (X Y Z : C) (s t : ℕ) :
    smashComposition unit X Y Z (s + 1) t ≫
        adamsSmashTowerStep unit (mappingObject X Z) (t + s) =
      (adamsSmashTowerStep unit (mappingObject X Y) s ▷
        adamsSmashTower unit (mappingObject Y Z) t) ≫
        smashComposition unit X Y Z s t := by
  have hin :
      ((adamsSmashSphereTensorIso unit (mappingObject X Y) (s + 1)).hom ⊗ₘ
        (adamsSmashSphereTensorIso unit (mappingObject Y Z) t).hom) ≫
        (adamsSmashTowerStep unit (mappingObject X Y) s ▷
          adamsSmashTower unit (mappingObject Y Z) t) =
      ((adamsSmashTowerStep unit (𝟙_ C) s ▷ mappingObject X Y) ▷
          (adamsSmashTower unit (𝟙_ C) t ⊗ mappingObject Y Z)) ≫
        ((adamsSmashSphereTensorIso unit (mappingObject X Y) s).hom ⊗ₘ
          (adamsSmashSphereTensorIso unit (mappingObject Y Z) t).hom) := by
    simp only [← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id,
      Category.id_comp, smashSphereTensorIso_step]
  have hcore := shuffle_pairing_naturality
    (adamsSmashTowerStep unit (𝟙_ C) s) (𝟙 (adamsSmashTower unit (𝟙_ C) t))
    (adamsSmashTowerStep unit (𝟙_ C) (t + s))
    (adamsSmashSpherePairingIso unit (s + 1) t).hom
    (adamsSmashSpherePairingIso unit s t).hom (Mapping.composition X Y Z)
    (by simpa only [tensorHom_id] using adamsSmashSpherePairingIso_step_left unit s t)
  have hc := congrArg (fun f => f ≫
    (adamsSmashSphereTensorIso unit (mappingObject X Z) (t + s)).hom) hcore
  simp only [id_whiskerRight, tensorHom_id, Category.assoc] at hc
  apply (cancel_epi
    ((adamsSmashSphereTensorIso unit (mappingObject X Y) (s + 1)).hom ⊗ₘ
      (adamsSmashSphereTensorIso unit (mappingObject Y Z) t).hom)).mp
  rw [← Category.assoc, smashComposition_coordinates]
  simp only [Category.assoc, Nat.add_succ]
  rw [smashSphereTensorIso_step, ← hc, ← smashComposition_coordinates]
  rw [← Category.assoc, ← hin, Category.assoc]

omit [MonoidalClosed C] [BraidedCategory C] in
private theorem smashSphereTensorIso_reindex (A : C) (a b : ℕ) (h : a = b) :
    (adamsSmashSphereTensorIso unit A a).hom ≫
        eqToHom (congrArg (adamsSmashTower unit A) h) =
      (eqToHom (congrArg (adamsSmashTower unit (𝟙_ C)) h) ▷ A) ≫
        (adamsSmashSphereTensorIso unit A b).hom := by
  subst b
  simp

/-- The second-input transition retains exactly the two-factor condition
needed by the existing ordered sphere concatenation. -/
theorem smashComposition_step_right (h : UnitFiberInclusionCommutes unit)
    (X Y Z : C) (s t : ℕ) :
    smashComposition unit X Y Z s (t + 1) ≫
        eqToHom (congrArg (adamsSmashTower unit (mappingObject X Z)) (Nat.succ_add t s)) ≫
        adamsSmashTowerStep unit (mappingObject X Z) (t + s) =
      (adamsSmashTower unit (mappingObject X Y) s ◁
        adamsSmashTowerStep unit (mappingObject Y Z) t) ≫
        smashComposition unit X Y Z s t := by
  have hin :
      ((adamsSmashSphereTensorIso unit (mappingObject X Y) s).hom ⊗ₘ
        (adamsSmashSphereTensorIso unit (mappingObject Y Z) (t + 1)).hom) ≫
        (adamsSmashTower unit (mappingObject X Y) s ◁
          adamsSmashTowerStep unit (mappingObject Y Z) t) =
      ((adamsSmashTower unit (𝟙_ C) s ⊗ mappingObject X Y) ◁
          (adamsSmashTowerStep unit (𝟙_ C) t ▷ mappingObject Y Z)) ≫
        ((adamsSmashSphereTensorIso unit (mappingObject X Y) s).hom ⊗ₘ
          (adamsSmashSphereTensorIso unit (mappingObject Y Z) t).hom) := by
    simp only [← id_tensorHom, tensorHom_comp_tensorHom, Category.comp_id,
      Category.id_comp, smashSphereTensorIso_step]
  have hout :
      (adamsSmashSphereTensorIso unit (mappingObject X Z) ((t + 1) + s)).hom ≫
        eqToHom (congrArg (adamsSmashTower unit (mappingObject X Z)) (Nat.succ_add t s)) ≫
        adamsSmashTowerStep unit (mappingObject X Z) (t + s) =
      ((eqToHom (congrArg (adamsSmashTower unit (𝟙_ C)) (Nat.succ_add t s)) ≫
        adamsSmashTowerStep unit (𝟙_ C) (t + s)) ▷ mappingObject X Z) ≫
        (adamsSmashSphereTensorIso unit (mappingObject X Z) (t + s)).hom := by
    rw [← Category.assoc,
      smashSphereTensorIso_reindex unit (mappingObject X Z) ((t + 1) + s)
        (t + s + 1) (Nat.succ_add t s), Category.assoc,
      smashSphereTensorIso_step]
    simp only [comp_whiskerRight, Category.assoc]
  have hcore := shuffle_pairing_naturality
    (𝟙 (adamsSmashTower unit (𝟙_ C) s)) (adamsSmashTowerStep unit (𝟙_ C) t)
    (eqToHom (congrArg (adamsSmashTower unit (𝟙_ C)) (Nat.succ_add t s)) ≫
      adamsSmashTowerStep unit (𝟙_ C) (t + s))
    (adamsSmashSpherePairingIso unit s (t + 1)).hom
    (adamsSmashSpherePairingIso unit s t).hom (Mapping.composition X Y Z)
    (by simpa only [adamsSmashSpherePairingNextRight, Category.assoc, id_tensorHom]
      using adamsSmashSpherePairingIso_step_right unit h s t)
  have hc := congrArg (fun f => f ≫
    (adamsSmashSphereTensorIso unit (mappingObject X Z) (t + s)).hom) hcore
  simp only [id_whiskerRight, id_tensorHom, Category.assoc] at hc
  apply (cancel_epi
    ((adamsSmashSphereTensorIso unit (mappingObject X Y) s).hom ⊗ₘ
      (adamsSmashSphereTensorIso unit (mappingObject Y Z) (t + 1)).hom)).mp
  rw [← Category.assoc, smashComposition_coordinates]
  simp only [Category.assoc]
  rw [hout, ← hc, ← smashComposition_coordinates]
  rw [← Category.assoc, ← hin, Category.assoc]

variable [∀ A : C, (tensorRight A).CommShift ℤ]
  [∀ A : C, (tensorRight A).IsTriangulated] [MonoidalPreadditive C]

/-- The existing iterated-fiber mapping towers inherit the first-input law
through their already proved transition-compatible smash comparisons. -/
theorem stageComposition_step_left (X Y Z : C) (s t : ℕ) :
    stageComposition unit X Y Z (s + 1) t ≫
        adamsTowerStep unit (mappingObject X Z) (t + s) =
      (adamsTowerStep unit (mappingObject X Y) s ▷ mappingStage unit Y Z t) ≫
        stageComposition unit X Y Z s t := by
  have htensor :
      ((adamsTowerSmashIso unit (mappingObject X Y) (s + 1)).hom ⊗ₘ
        (adamsTowerSmashIso unit (mappingObject Y Z) t).hom) ≫
        (adamsSmashTowerStep unit (mappingObject X Y) s ▷
          adamsSmashTower unit (mappingObject Y Z) t) =
      (adamsTowerStep unit (mappingObject X Y) s ▷ mappingStage unit Y Z t) ≫
        ((adamsTowerSmashIso unit (mappingObject X Y) s).hom ⊗ₘ
          (adamsTowerSmashIso unit (mappingObject Y Z) t).hom) := by
    simp only [← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id,
      Category.id_comp, adamsTowerSmashIso_step]
  apply (cancel_mono (adamsTowerSmashIso unit (mappingObject X Z) (t + s)).hom).mp
  have hc := stageComposition_comparison unit X Y Z (s + 1) t
  simp only [Nat.add_succ] at hc
  simp only [Category.assoc, ← adamsTowerSmashIso_step]
  rw [← Category.assoc, hc]
  simp only [Category.assoc]
  rw [smashComposition_step_left, ← Category.assoc, htensor, Category.assoc,
    ← stageComposition_comparison]

omit [MonoidalClosed C] [BraidedCategory C] [MonoidalPreadditive C] in
private theorem towerSmashIso_reindex (A : C) (a b : ℕ) (h : a = b) :
    eqToHom (congrArg (adamsTower unit A) h) ≫ (adamsTowerSmashIso unit A b).hom =
      (adamsTowerSmashIso unit A a).hom ≫ eqToHom (congrArg (adamsSmashTower unit A) h) := by
  subst b
  simp

/-- The second-input law on the same actual mapping towers, retaining the
necessary sphere-concatenation condition and the target index transport. -/
theorem stageComposition_step_right (h : UnitFiberInclusionCommutes unit)
    (X Y Z : C) (s t : ℕ) :
    stageComposition unit X Y Z s (t + 1) ≫
        eqToHom (congrArg (adamsTower unit (mappingObject X Z)) (Nat.succ_add t s)) ≫
        adamsTowerStep unit (mappingObject X Z) (t + s) =
      (mappingStage unit X Y s ◁ adamsTowerStep unit (mappingObject Y Z) t) ≫
        stageComposition unit X Y Z s t := by
  have htensor :
      ((adamsTowerSmashIso unit (mappingObject X Y) s).hom ⊗ₘ
        (adamsTowerSmashIso unit (mappingObject Y Z) (t + 1)).hom) ≫
        (adamsSmashTower unit (mappingObject X Y) s ◁
          adamsSmashTowerStep unit (mappingObject Y Z) t) =
      (mappingStage unit X Y s ◁ adamsTowerStep unit (mappingObject Y Z) t) ≫
        ((adamsTowerSmashIso unit (mappingObject X Y) s).hom ⊗ₘ
          (adamsTowerSmashIso unit (mappingObject Y Z) t).hom) := by
    simp only [← id_tensorHom, tensorHom_comp_tensorHom, Category.comp_id,
      Category.id_comp, adamsTowerSmashIso_step]
  have hout :
      eqToHom (congrArg (adamsTower unit (mappingObject X Z)) (Nat.succ_add t s)) ≫
        adamsTowerStep unit (mappingObject X Z) (t + s) ≫
        (adamsTowerSmashIso unit (mappingObject X Z) (t + s)).hom =
      (adamsTowerSmashIso unit (mappingObject X Z) ((t + 1) + s)).hom ≫
        eqToHom (congrArg (adamsSmashTower unit (mappingObject X Z)) (Nat.succ_add t s)) ≫
        adamsSmashTowerStep unit (mappingObject X Z) (t + s) := by
    rw [← adamsTowerSmashIso_step, ← Category.assoc,
      towerSmashIso_reindex unit (mappingObject X Z) ((t + 1) + s)
        (t + s + 1) (Nat.succ_add t s), Category.assoc]
  apply (cancel_mono (adamsTowerSmashIso unit (mappingObject X Z) (t + s)).hom).mp
  simp only [Category.assoc]
  rw [hout, ← Category.assoc, stageComposition_comparison]
  simp only [Category.assoc]
  rw [smashComposition_step_right unit h, ← Category.assoc, htensor, Category.assoc,
    ← stageComposition_comparison]

end
end KIP126.Classical.Adams.Moss
