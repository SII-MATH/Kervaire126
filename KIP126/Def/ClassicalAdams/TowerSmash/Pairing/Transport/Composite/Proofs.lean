module

public import KIP126.Def.ClassicalAdams.TowerSmash.Pairing.Transport.Proofs

@[expose] public section


namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H)
  [∀ Y : C, (tensorRight Y).CommShift ℤ]
  [∀ Y : C, (tensorRight Y).IsTriangulated] [MonoidalPreadditive C]

/-- The actual sphere-stage pairing commutes with any finite composite
in its first input. This is proved from the previously constructed successor
squares; neither a long-layer product nor a derivation law is assumed. -/
theorem adamsTowerSpherePairingIso_map_left (s z t : ℕ) (h : s ≤ z) :
    (adamsTowerSpherePairingIso unit z t).hom ≫
        adamsTowerMap unit (𝟙_ C) (t + s) (t + z) (by omega) =
      (adamsTowerMap unit (𝟙_ C) s z h ▷ adamsTower unit (𝟙_ C) t) ≫
        (adamsTowerSpherePairingIso unit s t).hom := by
  induction z, h using Nat.le_induction with
  | base => simp
  | succ z h ih =>
    simp only [Nat.add_succ]
    rw [adamsTowerMap_succ unit (𝟙_ C) (t + s) (t + z) (by omega),
      adamsTowerMap_succ unit (𝟙_ C) s z h, ← Category.assoc,
      adamsTowerSpherePairingIso_step_left, Category.assoc, ih,
      comp_whiskerRight, Category.assoc]

end
end KIP126.Classical.Adams
