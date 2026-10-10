import KIP126.Def.ClassicalAdams.TowerLongLayer.Page.Proofs

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- The actual long-cofiber connecting homomorphism followed by the target
layer-to-page map. This is defined from `k_r` and `j`, not from a postulated
derivation or an independently selected page differential. -/
def adamsLongLayerBoundaryToPage (r : ℕ) (hr : 1 ≤ r) (s t : ℤ) :
    HomotopyGroup (t - s) (adamsLongLayer unit X r hr s) →ₗ[ℤ]
      adamsPage unit X r hr (s + r) (t + r - 1) :=
  (adamsJToPage unit X r hr (s + r) (t + r - 1)).comp
    ((LinearEquiv.cast (R := ℤ)
      (M := fun k => HomotopyGroup k (adamsTowerAt unit X (s + r)))
      (by omega : t - s - 1 = (t + r - 1) - (s + r))).toLinearMap.comp
        (adamsLongLayerK unit X r hr s t))

end
end KIP126.Classical.Adams
