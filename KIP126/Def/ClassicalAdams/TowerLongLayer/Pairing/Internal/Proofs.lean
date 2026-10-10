import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Internal.Data

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} {unit : 𝟙_ C ⟶ H} {X : C}
  {n : ℕ} {p q : ℤ × ℤ}
  (P : AdamsLongLayerPairing unit X (n + 2) (by omega) p q)
  (hP : P.ProjectionCompatible) (hB : P.BoundaryCompatible)

theorem AdamsLongLayerPairing.onInternalPage_comparison (x y) :
    (adamsTowerSSDataPageIso unit X (p.1 + q.1) (p.2 + q.2) n).hom
        (P.onInternalPage hP hB x y) =
      P.onPage hP hB ((adamsTowerSSDataPageIso unit X p.1 p.2 n).hom x)
        ((adamsTowerSSDataPageIso unit X q.1 q.2 n).hom y) :=
  ModuleCat.hom_inv_apply _ _

theorem AdamsLongLayerPairing.onInternalPage_long (a b) :
    P.onInternalPage hP hB (adamsLongLayerToInternalPage unit X n p.1 p.2 a)
        (adamsLongLayerToInternalPage unit X n q.1 q.2 b) =
      adamsLongLayerToInternalPage unit X n (p.1 + q.1) (p.2 + q.2) (P.long a b) := by
  change (adamsTowerSSDataPageIso unit X (p.1 + q.1) (p.2 + q.2) n).inv
    (P.onPage hP hB ((adamsTowerSSDataPageIso unit X p.1 p.2 n).hom
      (adamsLongLayerToInternalPage unit X n p.1 p.2 a))
      ((adamsTowerSSDataPageIso unit X q.1 q.2 n).hom
        (adamsLongLayerToInternalPage unit X n q.1 q.2 b))) =
    (adamsTowerSSDataPageIso unit X (p.1 + q.1) (p.2 + q.2) n).inv _
  rw [adamsLongLayerToInternalPage_comparison, adamsLongLayerToInternalPage_comparison,
    P.onPage_long hP hB]

end
end KIP126.Classical.Adams
