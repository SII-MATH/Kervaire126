import KIP126.Def.ClassicalAdams.Moss.Composition.Transition.Proofs
import KIP126.Def.ClassicalAdams.TowerSmash.Pairing.Transport.Successor.Proofs

namespace KIP126.Classical.Adams.Moss

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [MonoidalClosed C] [BraidedCategory C]
  {H : C} (unit : 𝟙_ C ⟶ H)

omit [HasFunctorialCofiber (C := C)] [MonoidalClosed C] in
@[reassoc] private theorem shuffle_pairing_succ {K A B U V D E : C}
    (f : A ⊗ B ⟶ D) (g : U ⊗ V ⟶ E) :
    tensorμ (K ⊗ A) U B V ≫
      (((α_ K A B).hom ≫ K ◁ f) ⊗ₘ g) ≫ (α_ K D E).hom =
    ((α_ K A U).hom ▷ (B ⊗ V)) ≫
      (α_ K (A ⊗ U) (B ⊗ V)).hom ≫
      K ◁ (tensorμ A U B V ≫ (f ⊗ₘ g)) := by
  unfold tensorμ
  monoidal

private theorem smashComposition_succ (X Y Z : C) (s t : ℕ) :
    smashComposition unit X Y Z (s + 1) t =
      (α_ (fiber unit) (adamsSmashTower unit (mappingObject X Y) s)
        (adamsSmashTower unit (mappingObject Y Z) t)).hom ≫
        fiber unit ◁ smashComposition unit X Y Z s t := by
  apply (cancel_epi
    ((adamsSmashSphereTensorIso unit (mappingObject X Y) (s + 1)).hom ⊗ₘ
      (adamsSmashSphereTensorIso unit (mappingObject Y Z) t).hom)).mp
  rw [smashComposition_coordinates]
  simp only [adamsSmashSpherePairingIso_succ, Nat.add_succ,
    adamsSmashSphereTensorIso, Iso.trans_hom, Functor.mapIso_hom,
    tensorLeft, curriedTensor, adamsSmashTower, Nat.add_zero]
  erw [shuffle_pairing_succ_assoc]
  simp only [← whiskerLeft_comp, Category.assoc]
  erw [← smashComposition_coordinates unit X Y Z s t]
  monoidal

variable [∀ A : C, (tensorRight A).CommShift ℤ]
  [∀ A : C, (tensorRight A).IsTriangulated]

/-- In the existing fiber coordinates, the actual mapping-stage composition
at a left successor is the preceding composition tensored by the unit fiber.
This identifies the map itself, before composing with the fiber inclusion;
no boundary formula or page pairing is assumed. -/
theorem stageComposition_succ_comparison (X Y Z : C) (s t : ℕ) :
    stageComposition unit X Y Z (s + 1) t ≫
      (adamsFiberTensorIso unit (mappingStage unit X Z (t + s))).hom =
    ((adamsFiberTensorIso unit (mappingStage unit X Y s)).hom ▷
      mappingStage unit Y Z t) ≫
      (α_ (fiber unit) (mappingStage unit X Y s)
        (mappingStage unit Y Z t)).hom ≫
      fiber unit ◁ stageComposition unit X Y Z s t := by
  have hs (A : C) (k : ℕ) :
      (adamsFiberTensorIso unit (adamsTower unit A k)).hom ≫
        fiber unit ◁ (adamsTowerSmashIso unit A k).hom =
      (adamsTowerSmashIso unit A (k + 1)).hom := rfl
  apply (cancel_mono
    (fiber unit ◁ (adamsTowerSmashIso unit (mappingObject X Z) (t + s)).hom)).mp
  have hc := stageComposition_comparison unit X Y Z (s + 1) t
  simp only [Nat.add_succ] at hc
  erw [Category.assoc, hs, hc]
  rw [smashComposition_succ]
  change (((adamsFiberTensorIso unit (adamsTower unit (mappingObject X Y) s)).hom ≫
      fiber unit ◁ (adamsTowerSmashIso unit (mappingObject X Y) s).hom) ⊗ₘ
      (adamsTowerSmashIso unit (mappingObject Y Z) t).hom) ≫
      (α_ (fiber unit) (adamsSmashTower unit (mappingObject X Y) s)
        (adamsSmashTower unit (mappingObject Y Z) t)).hom ≫
      fiber unit ◁ smashComposition unit X Y Z s t = _
  simp only [Category.assoc, ← whiskerLeft_comp]
  rw [stageComposition_comparison]
  simp only [whiskerLeft_comp, tensorHom_def, Category.assoc, comp_whiskerRight]
  simp only [associator_naturality_middle_assoc, associator_naturality_right_assoc]

end
end KIP126.Classical.Adams.Moss
