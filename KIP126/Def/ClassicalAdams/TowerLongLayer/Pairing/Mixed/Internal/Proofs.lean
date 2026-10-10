import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Mixed.Internal.Data

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} {unit : 𝟙_ C ⟶ H} {X Y Z : C}
  {n : ℕ} {p q : ℤ × ℤ}
  (P : MixedAdamsLongLayerPairing unit X Y Z (n + 2) (by omega) p q)
  (hP : P.ProjectionCompatible) (hB : P.BoundaryCompatible)

theorem MixedAdamsLongLayerPairing.onInternalPage_comparison (x y) :
    (adamsTowerSSDataPageIso unit Z (p.1 + q.1) (p.2 + q.2) n).hom
        (P.onInternalPage hP hB x y) =
      P.onPage hP hB ((adamsTowerSSDataPageIso unit X p.1 p.2 n).hom x)
        ((adamsTowerSSDataPageIso unit Y q.1 q.2 n).hom y) :=
  ModuleCat.hom_inv_apply _ _

theorem MixedAdamsLongLayerPairing.onInternalPage_long (a b) :
    P.onInternalPage hP hB (adamsLongLayerToInternalPage unit X n p.1 p.2 a)
        (adamsLongLayerToInternalPage unit Y n q.1 q.2 b) =
      adamsLongLayerToInternalPage unit Z n (p.1 + q.1) (p.2 + q.2) (P.long a b) := by
  change (adamsTowerSSDataPageIso unit Z (p.1 + q.1) (p.2 + q.2) n).inv
    (P.onPage hP hB ((adamsTowerSSDataPageIso unit X p.1 p.2 n).hom
      (adamsLongLayerToInternalPage unit X n p.1 p.2 a))
      ((adamsTowerSSDataPageIso unit Y q.1 q.2 n).hom
        (adamsLongLayerToInternalPage unit Y n q.1 q.2 b))) =
    (adamsTowerSSDataPageIso unit Z (p.1 + q.1) (p.2 + q.2) n).inv _
  rw [adamsLongLayerToInternalPage_comparison, adamsLongLayerToInternalPage_comparison,
    P.onPage_long hP hB]

/-- The representative formula determines the mixed pairing on the actual
internal pages. Neither input is replaced by the output spectrum. -/
theorem MixedAdamsLongLayerPairing.onInternalPage_unique
    (F : (adamsTowerSSData unit X p.1 p.2).page (n : WithTop ℕ) →ₗ[ℤ]
      (adamsTowerSSData unit Y q.1 q.2).page (n : WithTop ℕ) →ₗ[ℤ]
        (adamsTowerSSData unit Z (p.1 + q.1) (p.2 + q.2)).page (n : WithTop ℕ))
    (hF : ∀ a b, F (adamsLongLayerToInternalPage unit X n p.1 p.2 a)
      (adamsLongLayerToInternalPage unit Y n q.1 q.2 b) =
        adamsLongLayerToInternalPage unit Z n (p.1 + q.1) (p.2 + q.2) (P.long a b)) :
    F = P.onInternalPage hP hB := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  obtain ⟨a, rfl⟩ := adamsLongLayerToInternalPage_surjective unit X n p.1 p.2 x
  obtain ⟨b, rfl⟩ := adamsLongLayerToInternalPage_surjective unit Y n q.1 q.2 y
  exact (hF a b).trans (P.onInternalPage_long hP hB a b).symm

end
end KIP126.Classical.Adams
