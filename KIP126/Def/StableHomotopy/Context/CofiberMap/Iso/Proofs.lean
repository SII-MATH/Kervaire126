import KIP126.Def.StableHomotopy.Context.Data

/-! An isomorphism square induces an isomorphism through the specified
cofiber map, by the actual morphism of distinguished triangles. -/

namespace KIP126.StableHomotopy

open CategoryTheory CategoryTheory.Pretriangulated

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]

/-- Both endpoints of an isomorphism square are isomorphisms, so its actual
chosen cofiber map is an isomorphism. No cofiber functor laws are needed. -/
theorem cofiberMap_isIso {X₁ Y₁ X₂ Y₂ : C}
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) (α : X₁ ⟶ X₂) (β : Y₁ ⟶ Y₂)
    (h : α ≫ g = f ≫ β) [IsIso α] [IsIso β] :
    IsIso (HasFunctorialCofiber.cofibMap f g α β h) := by
  let φ : Triangle.mk f (HasFunctorialCofiber.cofibι f) (HasFunctorialCofiber.cofibδ f) ⟶
      Triangle.mk g (HasFunctorialCofiber.cofibι g) (HasFunctorialCofiber.cofibδ g) :=
    { hom₁ := α
      hom₂ := β
      hom₃ := HasFunctorialCofiber.cofibMap f g α β h
      comm₁ := h.symm
      comm₂ := (HasFunctorialCofiber.cofibMap_ι f g α β h).symm
      comm₃ := (HasFunctorialCofiber.cofibMap_δ f g α β h).symm }
  exact isIso₃_of_isIso₁₂ φ (HasFunctorialCofiber.cofib_distinguished f)
    (HasFunctorialCofiber.cofib_distinguished g)
    (inferInstanceAs (IsIso α)) (inferInstanceAs (IsIso β))

end KIP126.StableHomotopy
