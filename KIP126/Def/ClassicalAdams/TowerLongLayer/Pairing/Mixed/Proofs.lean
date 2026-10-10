import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Mixed.Predicates
import KIP126.Def.ClassicalAdams.TowerLayer.Basic.Proofs

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} {unit : 𝟙_ C ⟶ H} {X Y Z : C}
  {r : ℕ} {hr : 1 ≤ r} {p q : ℤ × ℤ}
  (P : MixedAdamsLongLayerPairing unit X Y Z r hr p q)

/-- General cycles are closed under the specified first-page pairing when
it lifts to a compatible long-layer pairing. -/
theorem MixedAdamsLongLayerPairing.mem_cycles (hP : P.ProjectionCompatible)
    (x : adamsE1 unit X p.1 p.2) (hx : x ∈ adamsCycles unit X r hr p.1 p.2)
    (y : adamsE1 unit Y q.1 q.2) (hy : y ∈ adamsCycles unit Y r hr q.1 q.2) :
    P.first x y ∈ adamsCycles unit Z r hr (p.1 + q.1) (p.2 + q.2) := by
  obtain ⟨a, ha⟩ := (adamsCycles_mem_iff_longLayer unit X r hr p.1 p.2 x).mp hx
  obtain ⟨b, hb⟩ := (adamsCycles_mem_iff_longLayer unit Y r hr q.1 q.2 y).mp hy
  apply (adamsCycles_mem_iff_longLayer unit Z r hr _ _ _).mpr
  refine ⟨P.long a b, ?_⟩
  rw [hP a b, ha, hb]

theorem MixedAdamsLongLayerPairing.boundary_left (hB : P.BoundaryCompatible)
    (x : adamsE1 unit X p.1 p.2) (hx : x ∈ adamsBoundaries unit X r hr p.1 p.2)
    (y : adamsE1 unit Y q.1 q.2) (hy : y ∈ adamsCycles unit Y r hr q.1 q.2) :
    P.first x y ∈ adamsBoundaries unit Z r hr (p.1 + q.1) (p.2 + q.2) := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb⟩ := (adamsCycles_mem_iff_longLayer unit Y r hr q.1 q.2 y).mp hy
  rw [← hb]
  exact hB.left a ha b

theorem MixedAdamsLongLayerPairing.boundary_right (hB : P.BoundaryCompatible)
    (x : adamsE1 unit X p.1 p.2) (hx : x ∈ adamsCycles unit X r hr p.1 p.2)
    (y : adamsE1 unit Y q.1 q.2) (hy : y ∈ adamsBoundaries unit Y r hr q.1 q.2) :
    P.first x y ∈ adamsBoundaries unit Z r hr (p.1 + q.1) (p.2 + q.2) := by
  obtain ⟨b, hb, rfl⟩ := hy
  obtain ⟨a, ha⟩ := (adamsCycles_mem_iff_longLayer unit X r hr p.1 p.2 x).mp hx
  rw [← ha]
  exact hB.right a b hb

/-- At length one, both input boundary modules vanish. Boundary compatibility
is therefore a consequence for every mixed bilinear pairing, not an input. -/
theorem MixedAdamsLongLayerPairing.boundaryCompatible_one
    (Q : MixedAdamsLongLayerPairing unit X Y Z 1 le_rfl p q) : Q.BoundaryCompatible := by
  constructor
  · intro a ha b
    have hz : adamsJ unit X p.1 p.2 a = 0 := by
      have hb : adamsJ unit X p.1 p.2 a ∈ adamsBoundaries unit X 1 le_rfl p.1 p.2 :=
        ⟨a, ha, rfl⟩
      simpa only [adamsBoundaries_one, Submodule.mem_bot] using hb
    rw [hz, map_zero, LinearMap.zero_apply]
    exact Submodule.zero_mem _
  · intro a b hb
    have hz : adamsJ unit Y q.1 q.2 b = 0 := by
      have hc : adamsJ unit Y q.1 q.2 b ∈ adamsBoundaries unit Y 1 le_rfl q.1 q.2 :=
        ⟨b, hb, rfl⟩
      simpa only [adamsBoundaries_one, Submodule.mem_bot] using hc
    rw [hz, map_zero]
    exact Submodule.zero_mem _

end
end KIP126.Classical.Adams
