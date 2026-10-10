import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Internal.Proofs
import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Leibniz.Proofs

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} {unit : 𝟙_ C ⟶ H} {X : C}
  {n : ℕ} {p q : ℤ × ℤ}
  (P : AdamsLongLayerPairing unit X (n + 2) (by omega) p q)
  (hP : P.ProjectionCompatible) (hB : P.BoundaryCompatible)

/-- The relative boundary identity computes the existing internal
differential of the descended product. Both input differentials are also
the existing internal differentials, compared to their quotient pages. -/
theorem AdamsLongLayerPairing.internalD_of_relativeBoundary
    (L : adamsPage unit X (n + 2) (by omega) (p.1 + (n + 2 : ℕ))
      (p.2 + (n + 2 : ℕ) - 1) →ₗ[ℤ]
      adamsPage unit X (n + 2) (by omega) q.1 q.2 →ₗ[ℤ]
      adamsPage unit X (n + 2) (Nat.succ_le_succ (Nat.zero_le (n + 1))) ((p.1 + q.1) + (n + 2 : ℕ))
        ((p.2 + q.2) + (n + 2 : ℕ) - 1))
    (R : adamsPage unit X (n + 2) (by omega) p.1 p.2 →ₗ[ℤ]
      adamsPage unit X (n + 2) (by omega) (q.1 + (n + 2 : ℕ))
        (q.2 + (n + 2 : ℕ) - 1) →ₗ[ℤ]
      adamsPage unit X (n + 2) (Nat.succ_le_succ (Nat.zero_le (n + 1))) ((p.1 + q.1) + (n + 2 : ℕ))
        ((p.2 + q.2) + (n + 2 : ℕ) - 1))
    (e : ℤ) (h : P.RelativeBoundaryFormula L R e) (x y) :
    (adamsTowerSSDataPageIso unit X ((p.1 + q.1) + (n + 2 : ℕ))
      ((p.2 + q.2) + (n + 2 : ℕ) - 1) n).hom
      ((adamsTowerInternalD unit X n (p.1 + q.1) (p.2 + q.2))
        (P.onInternalPage hP hB x y)) =
      L ((adamsTowerSSDataPageIso unit X (p.1 + (n + 2 : ℕ))
          (p.2 + (n + 2 : ℕ) - 1) n).hom ((adamsTowerInternalD unit X n p.1 p.2) x))
        ((adamsTowerSSDataPageIso unit X q.1 q.2 n).hom y) +
      e • R ((adamsTowerSSDataPageIso unit X p.1 p.2 n).hom x)
        ((adamsTowerSSDataPageIso unit X (q.1 + (n + 2 : ℕ))
          (q.2 + (n + 2 : ℕ) - 1) n).hom ((adamsTowerInternalD unit X n q.1 q.2) y)) := by
  have hxy := ConcreteCategory.congr_hom
    (adamsTowerInternalD_comparison unit X n (p.1 + q.1) (p.2 + q.2))
    (P.onInternalPage hP hB x y)
  change _ = adamsDifferential unit X (n + 2) (by omega) (p.1 + q.1) (p.2 + q.2)
    ((adamsTowerSSDataPageIso unit X (p.1 + q.1) (p.2 + q.2) n).hom
      (P.onInternalPage hP hB x y)) at hxy
  rw [P.onInternalPage_comparison hP hB] at hxy
  have hx := ConcreteCategory.congr_hom (adamsTowerInternalD_comparison unit X n p.1 p.2) x
  have hy := ConcreteCategory.congr_hom (adamsTowerInternalD_comparison unit X n q.1 q.2) y
  change (adamsTowerSSDataPageIso unit X (p.1 + (n + 2 : ℕ))
    (p.2 + (n + 2 : ℕ) - 1) n).hom ((adamsTowerInternalD unit X n p.1 p.2) x) =
    adamsDifferential unit X (n + 2) (by omega) p.1 p.2
      ((adamsTowerSSDataPageIso unit X p.1 p.2 n).hom x) at hx
  change (adamsTowerSSDataPageIso unit X (q.1 + (n + 2 : ℕ))
    (q.2 + (n + 2 : ℕ) - 1) n).hom ((adamsTowerInternalD unit X n q.1 q.2) y) =
    adamsDifferential unit X (n + 2) (by omega) q.1 q.2
      ((adamsTowerSSDataPageIso unit X q.1 q.2 n).hom y) at hy
  rw [hx, hy]
  exact hxy.trans (P.leibniz_of_relativeBoundary hP hB L R e h _ _)

end
end KIP126.Classical.Adams
