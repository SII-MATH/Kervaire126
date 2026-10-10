import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Page.Data

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} {unit : 𝟙_ C ⟶ H} {X : C}
  {r : ℕ} {hr : 1 ≤ r} {p q : ℤ × ℤ}
  (P : AdamsLongLayerPairing unit X r hr p q)
  (hP : P.ProjectionCompatible) (hB : P.BoundaryCompatible)

@[simp] theorem AdamsLongLayerPairing.onPage_mk
    (x : adamsCycles unit X r hr p.1 p.2) (y : adamsCycles unit X r hr q.1 q.2) :
    P.onPage hP hB ((adamsCycleBoundaries unit X r hr p.1 p.2).mkQ x)
        ((adamsCycleBoundaries unit X r hr q.1 q.2).mkQ y) =
      (adamsCycleBoundaries unit X r hr (p.1 + q.1) (p.2 + q.2)).mkQ
        (P.onCycles hP x y) := rfl

/-- The descended pairing agrees with the supplied long-layer operation,
so the quotient construction retains its geometric representatives. -/
theorem AdamsLongLayerPairing.onPage_long (a b) :
    P.onPage hP hB (adamsLongLayerToPage unit X r hr p.1 p.2 a)
        (adamsLongLayerToPage unit X r hr q.1 q.2 b) =
      adamsLongLayerToPage unit X r hr (p.1 + q.1) (p.2 + q.2) (P.long a b) := by
  change (adamsCycleBoundaries unit X r hr (p.1 + q.1) (p.2 + q.2)).mkQ _ =
    (adamsCycleBoundaries unit X r hr (p.1 + q.1) (p.2 + q.2)).mkQ _
  congr 1
  apply Subtype.ext
  exact (hP a b).symm

/-- Agreement on long-layer representatives determines the pairing on all
page elements, since both long-layer projection maps are surjective. -/
theorem AdamsLongLayerPairing.onPage_unique
    (F : adamsPage unit X r hr p.1 p.2 →ₗ[ℤ]
      adamsPage unit X r hr q.1 q.2 →ₗ[ℤ]
        adamsPage unit X r hr (p.1 + q.1) (p.2 + q.2))
    (hF : ∀ a b, F (adamsLongLayerToPage unit X r hr p.1 p.2 a)
      (adamsLongLayerToPage unit X r hr q.1 q.2 b) =
        adamsLongLayerToPage unit X r hr (p.1 + q.1) (p.2 + q.2) (P.long a b)) :
    F = P.onPage hP hB := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  obtain ⟨a, rfl⟩ := adamsLongLayerToPage_surjective unit X r hr p.1 p.2 x
  obtain ⟨b, rfl⟩ := adamsLongLayerToPage_surjective unit X r hr q.1 q.2 y
  exact (hF a b).trans (P.onPage_long hP hB a b).symm

end
end KIP126.Classical.Adams
