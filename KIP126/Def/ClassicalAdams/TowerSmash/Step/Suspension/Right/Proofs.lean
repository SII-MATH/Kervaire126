import KIP126.Def.ClassicalAdams.TowerSmash.Step.Suspension.Right.Data
import KIP126.Def.ClassicalAdams.TowerSmash.Step.Suspension.Proofs
import KIP126.Def.StableHomotopy.Context.TensorSuspension.Braiding.Proofs

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory BraidedCategory KIP126.StableHomotopy

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [BraidedCategory C]
  {H : C} (unit : 𝟙_ C ⟶ H)
  [∀ Y : C, (tensorRight Y).CommShift ℤ]
  [∀ Y : C, (tensorRight Y).IsTriangulated]
  [∀ Y : C, (tensorLeft Y).CommShift ℤ]

/-- The second-input boundary formula determines a braided fiber lift.
This does not identify that lift with the ordered successor pairing of
the sphere tower. Both ambient suspension compatibilities are explicit. -/
theorem adamsFiberTensorPairingRight_δ
    (h : RightTensorSuspensionCompatibility (C := C))
    (hb : TensorSuspensionBraidingCompatibility (C := C))
    {X Y Z : C} (f : X ⊗ Y ⟶ Z) :
    ((α_ X H Y).inv ≫ ((β_ X H).hom ▷ Y) ≫ (α_ H X Y).hom ≫ H ◁ f) ≫
        (adamsFiberTriangle (adamsUnit unit Z)).mor₃ =
      (X ◁ (adamsFiberTriangle (adamsUnit unit Y)).mor₃) ≫
        (Functor.commShiftIso (tensorLeft X) (1 : ℤ)).hom.app (fiber (adamsUnit unit Y)) ≫
        (adamsFiberTensorPairingRight unit f)⟦(1 : ℤ)⟧' := by
  let k : fiber (adamsUnit unit Y) ⊗ X ⟶ fiber (adamsUnit unit Z) :=
    ((adamsFiberTensorIso unit Y).hom ▷ X) ≫ (α_ (fiber unit) Y X).hom ≫
      fiber unit ◁ ((β_ X Y).inv ≫ f) ≫ (adamsFiberTensorIso unit Z).inv
  have hf := adamsFiberTensorIso_pairing_δ unit h ((β_ X Y).inv ≫ f)
  have he := congrArg (fun g => g ≫ (adamsFiberTriangle (adamsUnit unit Z)).mor₃)
    (braidedTensorPairing_swap (H := H) f).symm
  have ha : ((β_ X (H ⊗ Y)).hom ≫ (α_ H Y X).hom ≫
      H ◁ ((β_ X Y).inv ≫ f)) ≫ (adamsFiberTriangle (adamsUnit unit Z)).mor₃ =
      (β_ X (H ⊗ Y)).hom ≫ ((α_ H Y X).hom ≫
        H ◁ ((β_ X Y).inv ≫ f) ≫ (adamsFiberTriangle (adamsUnit unit Z)).mor₃) := by
    simp only [Category.assoc]
  have hn : (β_ X (H ⊗ Y)).hom ≫
      (((adamsFiberTriangle (adamsUnit unit Y)).mor₃ ▷ X) ≫
        (Functor.commShiftIso (tensorRight X) (1 : ℤ)).hom.app (fiber (adamsUnit unit Y)) ≫
        k⟦(1 : ℤ)⟧') =
      (X ◁ (adamsFiberTriangle (adamsUnit unit Y)).mor₃) ≫
        (Functor.commShiftIso (tensorLeft X) (1 : ℤ)).hom.app (fiber (adamsUnit unit Y)) ≫
        ((β_ X (fiber (adamsUnit unit Y))).hom ≫ k)⟦(1 : ℤ)⟧' :=
    braidedSuspension_transport hb X (adamsFiberTriangle (adamsUnit unit Y)).mor₃ k
  exact he.trans (ha.trans
    ((congrArg (fun g => (β_ X (H ⊗ Y)).hom ≫ g) hf).trans hn))

end
end KIP126.Classical.Adams
