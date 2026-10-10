import KIP126.Def.ClassicalAdams.TowerSmash.Step.Suspension.Right.Data
import KIP126.Def.ClassicalAdams.TowerSmash.Pairing.Transport.Data

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [BraidedCategory C]
  {H : C} (unit : 𝟙_ C ⟶ H)
  [∀ Y : C, (tensorRight Y).CommShift ℤ]
  [∀ Y : C, (tensorRight Y).IsTriangulated]

/-- The braided successor map forced by the second-input coefficient
boundary calculation. This is a map on the existing tower stages, not a
replacement tower or an assumed equality with `PairingNextRight`. -/
def adamsTowerSpherePairingBoundaryRight (s t : ℕ) :
    adamsTower unit (𝟙_ C) s ⊗ adamsTower unit (𝟙_ C) (t + 1) ⟶
      adamsTower unit (𝟙_ C) (t + s + 1) :=
  adamsFiberTensorPairingRight unit (adamsTowerSpherePairingIso unit s t).hom

end
end KIP126.Classical.Adams
