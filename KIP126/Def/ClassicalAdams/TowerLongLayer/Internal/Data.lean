import KIP126.Def.ClassicalAdams.TowerLongLayer.Page.Proofs
import KIP126.Def.ClassicalAdams.TowerSSData.Differential.Proofs

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- Long-layer representatives in the existing internal SSData page.
Internal index `n` is classical page `n+2`; no Mathlib SS adapter is used. -/
def adamsLongLayerToInternalPage (n : ℕ) (s t : ℤ) :
    HomotopyGroup (t - s) (adamsLongLayer unit X (n + 2) (by omega) s) →ₗ[ℤ]
      (adamsTowerSSData unit X s t).page (n : WithTop ℕ) :=
  (adamsTowerSSDataPageIso unit X s t n).inv.hom.comp
    (adamsLongLayerToPage unit X (n + 2) (by omega) s t)

end
end KIP126.Classical.Adams
