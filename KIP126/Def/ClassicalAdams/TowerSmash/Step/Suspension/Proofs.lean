import KIP126.Def.ClassicalAdams.TowerSmash.Step.Proofs
import KIP126.Def.StableHomotopy.Context.TensorSuspension.Proofs

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H)
  [∀ Y : C, (tensorRight Y).CommShift ℤ]
  [∀ Y : C, (tensorRight Y).IsTriangulated]

/-- Under explicit ambient suspension compatibility, the coefficient-side
pairing intertwines the actual Adams fiber connecting maps with the pairing
of fibers obtained from the already constructed tensor comparisons. -/
theorem adamsFiberTensorIso_pairing_δ
    (h : RightTensorSuspensionCompatibility (C := C))
    {X Y Z : C} (f : X ⊗ Y ⟶ Z) :
    (α_ H X Y).hom ≫ H ◁ f ≫ (adamsFiberTriangle (adamsUnit unit Z)).mor₃ =
      ((adamsFiberTriangle (adamsUnit unit X)).mor₃ ▷ Y) ≫
        (Functor.commShiftIso (tensorRight Y) (1 : ℤ)).hom.app
          (fiber (adamsUnit unit X)) ≫
        (((adamsFiberTensorIso unit X).hom ▷ Y) ≫
          (α_ (fiber unit) X Y).hom ≫ fiber unit ◁ f ≫
          (adamsFiberTensorIso unit Z).inv)⟦(1 : ℤ)⟧' := by
  let δ : H ⟶ (fiber unit)⟦(1 : ℤ)⟧ := (adamsFiberTriangle unit).mor₃
  let c (W B : C) : B⟦(1 : ℤ)⟧ ⊗ W ⟶ (B ⊗ W)⟦(1 : ℤ)⟧ :=
    (Functor.commShiftIso (tensorRight W) (1 : ℤ)).hom.app B
  change (α_ H X Y).hom ≫ H ◁ f ≫ (adamsFiberTriangle (adamsUnit unit Z)).mor₃ =
    ((adamsFiberTriangle (adamsUnit unit X)).mor₃ ▷ Y) ≫
      c Y (fiber (adamsUnit unit X)) ≫
      (((adamsFiberTensorIso unit X).hom ▷ Y) ≫
        (α_ (fiber unit) X Y).hom ≫ fiber unit ◁ f ≫
        (adamsFiberTensorIso unit Z).inv)⟦(1 : ℤ)⟧'
  have hd (W : C) : (δ ▷ W) ≫
      c W (fiber unit) ≫
      (adamsFiberTensorIso unit W).inv⟦(1 : ℤ)⟧' =
      (adamsFiberTriangle (adamsUnit unit W)).mor₃ :=
    adamsFiberTensorIso_inv_δ unit W
  rw [← hd Z, ← hd X]
  change (α_ H X Y).hom ≫ H ◁ f ≫ (δ ▷ Z) ≫ c Z (fiber unit) ≫
      (adamsFiberTensorIso unit Z).inv⟦(1 : ℤ)⟧' =
    (((δ ▷ X) ≫ c X (fiber unit) ≫ (adamsFiberTensorIso unit X).inv⟦(1 : ℤ)⟧') ▷ Y) ≫
      c Y (fiber (adamsUnit unit X)) ≫
      (((adamsFiberTensorIso unit X).hom ▷ Y) ≫ (α_ (fiber unit) X Y).hom ≫
        fiber unit ◁ f ≫ (adamsFiberTensorIso unit Z).inv)⟦(1 : ℤ)⟧'
  simp only [Functor.map_comp, comp_whiskerRight, Category.assoc]
  have hn : ((adamsFiberTensorIso unit X).inv⟦(1 : ℤ)⟧' ▷ Y) ≫
      c Y (fiber (adamsUnit unit X)) =
      c Y (fiber unit ⊗ X) ≫ ((adamsFiberTensorIso unit X).inv ▷ Y)⟦(1 : ℤ)⟧' :=
    Functor.commShiftIso_hom_naturality (tensorRight Y) (adamsFiberTensorIso unit X).inv 1
  rw [← Category.assoc ((adamsFiberTensorIso unit X).inv⟦(1 : ℤ)⟧' ▷ Y), hn]
  have hc : ((adamsFiberTensorIso unit X).inv ▷ Y)⟦(1 : ℤ)⟧' ≫
      ((adamsFiberTensorIso unit X).hom ▷ Y)⟦(1 : ℤ)⟧' =
      𝟙 (((fiber unit ⊗ X) ⊗ Y)⟦(1 : ℤ)⟧) :=
    ((shiftFunctor C (1 : ℤ)).mapIso
      ((tensorRight Y).mapIso (adamsFiberTensorIso unit X))).inv_hom_id
  simp only [Category.assoc]
  erw [← Category.assoc (((adamsFiberTensorIso unit X).inv ▷ Y)⟦(1 : ℤ)⟧'),
    hc, Category.id_comp]
  have hp : (α_ H X Y).hom ≫ H ◁ f ≫ (δ ▷ Z) ≫ c Z (fiber unit) =
      (((δ ▷ X) ≫ c X (fiber unit)) ▷ Y) ≫ c Y (fiber unit ⊗ X) ≫
        ((α_ (fiber unit) X Y).hom ≫ fiber unit ◁ f)⟦(1 : ℤ)⟧' :=
    rightTensorSuspension_pairing h δ f
  simpa only [Functor.map_comp, comp_whiskerRight, Category.assoc] using
    congrArg (fun g => g ≫ (adamsFiberTensorIso unit Z).inv⟦(1 : ℤ)⟧') hp

end
end KIP126.Classical.Adams
