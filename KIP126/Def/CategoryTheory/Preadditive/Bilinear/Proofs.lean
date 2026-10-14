module

public import Mathlib.CategoryTheory.Preadditive.Basic

@[expose] public section

namespace KIP126.Foundation

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C] [∀ X Y : C, AddGroup (X ⟶ Y)]

/-- Group operations on all hom sets that distribute through composition
are necessarily commutative. Expand the same composite in both orders
and cancel its outer summands. -/
theorem hom_add_comm_of_bilinear
    (add_comp : ∀ {X Y Z : C} (f g : X ⟶ Y) (h : Y ⟶ Z),
      (f + g) ≫ h = f ≫ h + g ≫ h)
    (comp_add : ∀ {X Y Z : C} (f : X ⟶ Y) (g h : Y ⟶ Z),
      f ≫ (g + h) = f ≫ g + f ≫ h)
    {X Y : C} (f g : X ⟶ Y) : f + g = g + f := by
  have h : (f + g) + (f + g) = (f + f) + (g + g) := by
    calc
      _ = (𝟙 X + 𝟙 X) ≫ (f + g) := by rw [add_comp]; simp only [Category.id_comp]
      _ = _ := by rw [comp_add, add_comp, add_comp]; simp only [Category.id_comp]
  have h' : g + f = f + g := by
    apply add_left_cancel (a := f)
    apply add_right_cancel (b := g)
    simpa only [add_assoc] using h
  exact h'.symm

end KIP126.Foundation
