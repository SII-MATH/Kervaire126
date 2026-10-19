module

public import KIP126.Def.CategoryTheory.Preadditive.Bilinear.Proofs

@[expose] public section

namespace KIP126.Foundation

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C] [∀ X Y : C, AddGroup (X ⟶ Y)]

/-- Package the original hom-group operations as a preadditive structure.
Commutativity is proved from bilinearity, rather than supplied separately. -/
@[implicit_reducible]
def preadditiveOfBilinearHomGroups
    (add_comp : ∀ {X Y Z : C} (f g : X ⟶ Y) (h : Y ⟶ Z),
      (f + g) ≫ h = f ≫ h + g ≫ h)
    (comp_add : ∀ {X Y Z : C} (f : X ⟶ Y) (g h : Y ⟶ Z),
      f ≫ (g + h) = f ≫ g + f ≫ h) : Preadditive C where
  homGroup X Y := { (inferInstance : AddGroup (X ⟶ Y)) with
    add_comm := hom_add_comm_of_bilinear add_comp comp_add }
  add_comp _ _ _ := add_comp
  comp_add _ _ _ := comp_add

end KIP126.Foundation
