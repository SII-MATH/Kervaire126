import KIP126.Def.StableHomotopy.Context.CofiberMap.Iso.Proofs

/-! Bundle the actual cofiber map of an isomorphism square as an iso. -/

namespace KIP126.StableHomotopy

open CategoryTheory

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]

/-- The specified cofiber map, with its proven invertibility. This does not
select an independent isomorphism between the cofiber objects. -/
noncomputable def cofiberMapIso {X₁ Y₁ X₂ Y₂ : C}
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) (α : X₁ ⟶ X₂) (β : Y₁ ⟶ Y₂)
    (h : α ≫ g = f ≫ β) [IsIso α] [IsIso β] :
    HasFunctorialCofiber.cofib f ≅ HasFunctorialCofiber.cofib g := by
  letI := cofiberMap_isIso f g α β h
  exact asIso (HasFunctorialCofiber.cofibMap f g α β h)

end KIP126.StableHomotopy
