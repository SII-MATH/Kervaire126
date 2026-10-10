import KIP126.Def.ClassicalAdams.Moss.Convergence.Data

namespace KIP126.Classical.Adams.Moss

open CategoryTheory CategoryTheory.MonoidalCategory KIP126.StableHomotopy

universe u v
noncomputable section

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [MonoidalClosed C]
  {H : C} (unit : 𝟙_ C ⟶ H) (X Y : C)

/-- The categorical filtration used for detection has precisely the same
image as the actual tower projection. This is a theorem, not an input field. -/
theorem mappingFiltration_image (s n : ℤ) (f : mappingAbutment X Y n) :
    (∃ a : (Subobject.underlying.obj
        ((mappingFiltration unit X Y).F s n) : ModuleCat.{v} ℤ),
      ((mappingFiltration unit X Y).F s n).arrow a = f) ↔
    ∃ g : HomotopyGroup n (mappingStage unit X Y s.toNat),
      g ≫ mappingToTarget unit X Y s.toNat = f := by
  change f ∈ (ModuleCat.subobjectModule _)
    ((ModuleCat.subobjectModule _).symm (mappingFiltrationSubmodule unit X Y s n)) ↔ _
  rw [OrderIso.apply_symm_apply]
  rfl

end
end KIP126.Classical.Adams.Moss
