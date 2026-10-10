import KIP126.Def.ClassicalAdams.TowerSmash.Pairing.Right.Proofs
import KIP126.Def.ClassicalAdams.TowerSmash.Pairing.Transport.Proofs

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H)
  [∀ Y : C, (tensorRight Y).CommShift ℤ]
  [∀ Y : C, (tensorRight Y).IsTriangulated]

/-- The already constructed actual tower pairing, with only its successor
target reindexed. No further pairing is chosen. -/
def adamsTowerSpherePairingNextRight (s t : ℕ) :
    adamsTower unit (𝟙_ C) s ⊗ adamsTower unit (𝟙_ C) (t + 1) ⟶
      adamsTower unit (𝟙_ C) (t + s + 1) :=
  (adamsTowerSpherePairingIso unit s (t + 1)).hom ≫
    eqToHom (congrArg (adamsTower unit (𝟙_ C)) (Nat.succ_add t s))

end
end KIP126.Classical.Adams
