import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Predicates

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} {unit : 𝟙_ C ⟶ H} {X : C}
  {r : ℕ} {hr : 1 ≤ r} {p q : ℤ × ℤ}
  (P : AdamsLongLayerPairing unit X r hr p q)

/-- General cycles are closed under the specified first-page pairing when
it lifts to a compatible long-layer pairing. -/
theorem AdamsLongLayerPairing.mem_cycles (hP : P.ProjectionCompatible)
    (x : adamsE1 unit X p.1 p.2) (hx : x ∈ adamsCycles unit X r hr p.1 p.2)
    (y : adamsE1 unit X q.1 q.2) (hy : y ∈ adamsCycles unit X r hr q.1 q.2) :
    P.first x y ∈ adamsCycles unit X r hr (p.1 + q.1) (p.2 + q.2) := by
  obtain ⟨a, ha⟩ := (adamsCycles_mem_iff_longLayer unit X r hr p.1 p.2 x).mp hx
  obtain ⟨b, hb⟩ := (adamsCycles_mem_iff_longLayer unit X r hr q.1 q.2 y).mp hy
  apply (adamsCycles_mem_iff_longLayer unit X r hr _ _ _).mpr
  refine ⟨P.long a b, ?_⟩
  rw [hP a b, ha, hb]

theorem AdamsLongLayerPairing.boundary_left (hB : P.BoundaryCompatible)
    (x : adamsE1 unit X p.1 p.2) (hx : x ∈ adamsBoundaries unit X r hr p.1 p.2)
    (y : adamsE1 unit X q.1 q.2) (hy : y ∈ adamsCycles unit X r hr q.1 q.2) :
    P.first x y ∈ adamsBoundaries unit X r hr (p.1 + q.1) (p.2 + q.2) := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb⟩ := (adamsCycles_mem_iff_longLayer unit X r hr q.1 q.2 y).mp hy
  rw [← hb]
  exact hB.left a ha b

theorem AdamsLongLayerPairing.boundary_right (hB : P.BoundaryCompatible)
    (x : adamsE1 unit X p.1 p.2) (hx : x ∈ adamsCycles unit X r hr p.1 p.2)
    (y : adamsE1 unit X q.1 q.2) (hy : y ∈ adamsBoundaries unit X r hr q.1 q.2) :
    P.first x y ∈ adamsBoundaries unit X r hr (p.1 + q.1) (p.2 + q.2) := by
  obtain ⟨b, hb, rfl⟩ := hy
  obtain ⟨a, ha⟩ := (adamsCycles_mem_iff_longLayer unit X r hr p.1 p.2 x).mp hx
  rw [← ha]
  exact hB.right a b hb

end
end KIP126.Classical.Adams
