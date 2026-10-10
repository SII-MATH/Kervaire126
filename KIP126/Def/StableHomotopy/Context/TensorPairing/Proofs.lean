import KIP126.Def.StableHomotopy.Context.TensorPairing.Data

namespace KIP126.StableHomotopy

noncomputable section
open CategoryTheory MonoidalCategory
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]

theorem tensorHomPairing_apply {A B W X Y Z : C}
    (w : W ⟶ A ⊗ B) (f : X ⊗ Y ⟶ Z) (x : A ⟶ X) (y : B ⟶ Y) :
    tensorHomPairing w f x y = w ≫ (x ⊗ₘ y) ≫ f := rfl

/-- A commuting square of spectrum pairings induces the represented square.
No independent compatibility assumption on the homotopy pairing is needed. -/
theorem tensorHomPairing_naturality {A B W X Y Z X' Y' Z' : C}
    (w : W ⟶ A ⊗ B) (f : X ⊗ Y ⟶ Z) (g : X' ⊗ Y' ⟶ Z')
    (i : X ⟶ X') (j : Y ⟶ Y') (k : Z ⟶ Z')
    (h : f ≫ k = (i ⊗ₘ j) ≫ g) (x : A ⟶ X) (y : B ⟶ Y) :
    tensorHomPairing w f x y ≫ k = tensorHomPairing w g (x ≫ i) (y ≫ j) := by
  simp only [tensorHomPairing_apply, Category.assoc, h,
    ← tensorHom_comp_tensorHom]

theorem homotopyTensorPairing_naturality (a b n : ℤ) (hn : n = a + b)
    [(tensorRight (Sphere b : C)).CommShift ℤ] {X Y Z X' Y' Z' : C}
    (f : X ⊗ Y ⟶ Z) (g : X' ⊗ Y' ⟶ Z')
    (i : X ⟶ X') (j : Y ⟶ Y') (k : Z ⟶ Z')
    (h : f ≫ k = (i ⊗ₘ j) ≫ g)
    (x : HomotopyGroup a X) (y : HomotopyGroup b Y) :
    inducedMap k n (homotopyTensorPairing a b n hn f x y) =
      homotopyTensorPairing a b n hn g (inducedMap i a x) (inducedMap j b y) :=
  tensorHomPairing_naturality _ f g i j k h x y

end
end KIP126.StableHomotopy
