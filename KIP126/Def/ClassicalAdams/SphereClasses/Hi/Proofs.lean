import KIP126.Def.ClassicalAdams.SphereClasses.Hi.Data

/-! Compatibility of the standard family with the existing `h₆` and square. -/

namespace KIP126.Classical.Adams.Sphere

noncomputable section

open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  (H : Mod2EilenbergMacLane (C := C)) (M : MilnorCooperations H)

@[simp] theorem hi_six : hi H M 6 = h6 H M := rfl

@[simp] theorem hiSquare_six : hiSquare H M 6 = h6Square H M := rfl

end

end KIP126.Classical.Adams.Sphere
