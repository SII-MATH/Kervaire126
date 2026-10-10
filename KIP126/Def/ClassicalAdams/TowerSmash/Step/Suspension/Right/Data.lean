import KIP126.Def.ClassicalAdams.TowerSmash.Step.Proofs

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory BraidedCategory KIP126.StableHomotopy

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [BraidedCategory C]
  {H : C} (unit : 𝟙_ C ⟶ H)
  [∀ Y : C, (tensorRight Y).CommShift ℤ]
  [∀ Y : C, (tensorRight Y).IsTriangulated]

/-- The fiber-level map occurring in the second-input boundary calculation.
It is determined by the original pairing and the existing fiber comparisons.
It must not be silently identified with a separately prescribed tower lift. -/
def adamsFiberTensorPairingRight {X Y Z : C} (f : X ⊗ Y ⟶ Z) :
    X ⊗ fiber (adamsUnit unit Y) ⟶ fiber (adamsUnit unit Z) :=
  (β_ X (fiber (adamsUnit unit Y))).hom ≫
    ((adamsFiberTensorIso unit Y).hom ▷ X) ≫ (α_ (fiber unit) Y X).hom ≫
    fiber unit ◁ ((β_ X Y).inv ≫ f) ≫ (adamsFiberTensorIso unit Z).inv

end
end KIP126.Classical.Adams
