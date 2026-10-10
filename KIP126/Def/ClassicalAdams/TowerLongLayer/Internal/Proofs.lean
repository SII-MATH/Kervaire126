import KIP126.Def.ClassicalAdams.TowerLongLayer.Internal.Data

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

theorem adamsLongLayerToInternalPage_comparison (n : ℕ) (s t : ℤ)
    (z : HomotopyGroup (t - s) (adamsLongLayer unit X (n + 2) (by omega) s)) :
    (adamsTowerSSDataPageIso unit X s t n).hom
        (adamsLongLayerToInternalPage unit X n s t z) =
      adamsLongLayerToPage unit X (n + 2) (by omega) s t z :=
  ModuleCat.hom_inv_apply _ _

theorem adamsLongLayerToInternalPage_surjective (n : ℕ) (s t : ℤ) :
    Function.Surjective (adamsLongLayerToInternalPage unit X n s t) := by
  intro x
  obtain ⟨z, hz⟩ := adamsLongLayerToPage_surjective unit X (n + 2) (by omega) s t
    ((adamsTowerSSDataPageIso unit X s t n).hom x)
  refine ⟨z, ?_⟩
  change (adamsTowerSSDataPageIso unit X s t n).inv
    (adamsLongLayerToPage unit X (n + 2) (by omega) s t z) = x
  rw [hz, ModuleCat.inv_hom_apply]

/-- The long-cofiber boundary computes the differential actually used by
the internal SSData/PreSS sequence, after its existing target comparison. -/
theorem adamsTowerInternalD_longLayer (n : ℕ) (s t : ℤ)
    (z : HomotopyGroup (t - s) (adamsLongLayer unit X (n + 2) (by omega) s)) :
    (adamsTowerSSDataPageIso unit X (s + (n + 2 : ℕ))
        (t + (n + 2 : ℕ) - 1) n).hom
      ((adamsTowerInternalD unit X n s t) (adamsLongLayerToInternalPage unit X n s t z)) =
      adamsJToPage unit X (n + 2) (by omega)
        (s + (n + 2 : ℕ)) (t + (n + 2 : ℕ) - 1)
        (Eq.mp (congrArg (fun k => HomotopyGroup k
          (adamsTowerAt unit X (s + (n + 2 : ℕ))))
          (by omega : t - s - 1 = (t + (n + 2 : ℕ) - 1) - (s + (n + 2 : ℕ))))
          (adamsLongLayerK unit X (n + 2) (by omega) s t z)) := by
  have hc := ConcreteCategory.congr_hom (adamsTowerInternalD_comparison unit X n s t)
    (adamsLongLayerToInternalPage unit X n s t z)
  change _ = adamsDifferential unit X (n + 2) (by omega) s t
    ((adamsTowerSSDataPageIso unit X s t n).hom
      (adamsLongLayerToInternalPage unit X n s t z)) at hc
  rw [adamsLongLayerToInternalPage_comparison] at hc
  exact hc.trans (adamsDifferential_longLayerToPage unit X (n + 2) (by omega) s t z)

end
end KIP126.Classical.Adams
