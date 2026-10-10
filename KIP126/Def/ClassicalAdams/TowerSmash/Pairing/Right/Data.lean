import KIP126.Def.ClassicalAdams.TowerSmash.Pairing.Proofs

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H)

/-- The existing concatenation map with its right-input successor target
reindexed from `(t+1)+s` to `(t+s)+1`. No new pairing is chosen. -/
def adamsSmashSpherePairingNextRight (s t : ℕ) :
    adamsSmashTower unit (𝟙_ C) s ⊗ adamsSmashTower unit (𝟙_ C) (t + 1) ⟶
      adamsSmashTower unit (𝟙_ C) (t + s + 1) :=
  (adamsSmashSpherePairingIso unit s (t + 1)).hom ≫
    eqToHom (congrArg (adamsSmashTower unit (𝟙_ C)) (Nat.succ_add t s))

end
end KIP126.Classical.Adams
