import KIP126.Def.ClassicalAdams.TowerSmash.Pairing.Right.Boundary.Data
import KIP126.Def.ClassicalAdams.TowerSmash.Step.Suspension.Right.Proofs
import KIP126.Def.ClassicalAdams.TowerSmash.Pairing.Right.Transport.Data

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

/-- The second-input coefficient boundary has this particular braided
lift. Its equality with the ordered tower successor is a separate question. -/
theorem adamsTowerSpherePairingBoundaryRight_δ
    (h : RightTensorSuspensionCompatibility (C := C))
    (hb : TensorSuspensionBraidingCompatibility (C := C)) (s t : ℕ) :
    ((α_ (adamsTower unit (𝟙_ C) s) H (adamsTower unit (𝟙_ C) t)).inv ≫
      ((β_ (adamsTower unit (𝟙_ C) s) H).hom ▷ adamsTower unit (𝟙_ C) t) ≫
      (α_ H (adamsTower unit (𝟙_ C) s) (adamsTower unit (𝟙_ C) t)).hom ≫
      H ◁ (adamsTowerSpherePairingIso unit s t).hom) ≫
      (adamsFiberTriangle (adamsUnit unit (adamsTower unit (𝟙_ C) (t + s)))).mor₃ =
    (adamsTower unit (𝟙_ C) s ◁
      (adamsFiberTriangle (adamsUnit unit (adamsTower unit (𝟙_ C) t))).mor₃) ≫
      (Functor.commShiftIso (tensorLeft (adamsTower unit (𝟙_ C) s)) (1 : ℤ)).hom.app
        (adamsTower unit (𝟙_ C) (t + 1)) ≫
      (adamsTowerSpherePairingBoundaryRight unit s t)⟦(1 : ℤ)⟧' :=
  adamsFiberTensorPairingRight_δ unit h hb (adamsTowerSpherePairingIso unit s t).hom

/-- The precise remaining comparison is vanishing of the difference of
the two lifts after the actual boundary, not necessarily equality of the
lifts themselves. This theorem does not supply that vanishing. -/
theorem adamsTowerSpherePairingBoundaryRight_obstruction (s t : ℕ) :
    ((adamsTower unit (𝟙_ C) s ◁
      (adamsFiberTriangle (adamsUnit unit (adamsTower unit (𝟙_ C) t))).mor₃) ≫
      (Functor.commShiftIso (tensorLeft (adamsTower unit (𝟙_ C) s)) (1 : ℤ)).hom.app
        (adamsTower unit (𝟙_ C) (t + 1)) ≫
      (adamsTowerSpherePairingBoundaryRight unit s t)⟦(1 : ℤ)⟧' =
    (adamsTower unit (𝟙_ C) s ◁
      (adamsFiberTriangle (adamsUnit unit (adamsTower unit (𝟙_ C) t))).mor₃) ≫
      (Functor.commShiftIso (tensorLeft (adamsTower unit (𝟙_ C) s)) (1 : ℤ)).hom.app
        (adamsTower unit (𝟙_ C) (t + 1)) ≫
      (adamsTowerSpherePairingNextRight unit s t)⟦(1 : ℤ)⟧') ↔
    (adamsTower unit (𝟙_ C) s ◁
      (adamsFiberTriangle (adamsUnit unit (adamsTower unit (𝟙_ C) t))).mor₃) ≫
      (Functor.commShiftIso (tensorLeft (adamsTower unit (𝟙_ C) s)) (1 : ℤ)).hom.app
        (adamsTower unit (𝟙_ C) (t + 1)) ≫
      (adamsTowerSpherePairingBoundaryRight unit s t -
        adamsTowerSpherePairingNextRight unit s t)⟦(1 : ℤ)⟧' = 0 := by
  have hsub {A B U V : C} (a : A ⟶ B) (b : B ⟶ U⟦(1 : ℤ)⟧)
      (f g : U ⟶ V) :
      (a ≫ b ≫ f⟦(1 : ℤ)⟧' = a ≫ b ≫ g⟦(1 : ℤ)⟧') ↔
        a ≫ b ≫ (f - g)⟦(1 : ℤ)⟧' = 0 := by
    simp only [Functor.map_sub, Preadditive.comp_sub, sub_eq_zero]
  exact hsub _ _ _ _

end
end KIP126.Classical.Adams
