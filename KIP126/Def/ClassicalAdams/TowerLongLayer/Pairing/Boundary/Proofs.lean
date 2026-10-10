import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Predicates

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} {unit : 𝟙_ C ⟶ H} {X : C}
  {r : ℕ} {hr : 1 ≤ r} {p q : ℤ × ℤ}

/-- A tower-kernel representative projects to zero when the corresponding
boundary submodule vanishes. -/
theorem adamsJ_eq_zero_of_boundaries_eq_bot (s t : ℤ)
    (hB : adamsBoundaries unit X r hr s t = ⊥)
    (a : HomotopyGroup (t - s) (adamsTowerAt unit X s))
    (ha : adamsI unit X (t - s) (s - r + 1) s (by omega) a = 0) :
    adamsJ unit X s t a = 0 := by
  have hb : adamsJ unit X s t a ∈ adamsBoundaries unit X r hr s t := ⟨a, ha, rfl⟩
  simpa only [hB, Submodule.mem_bot] using hb

/-- If neither input degree has boundaries, any bilinear representative
pairing satisfies both descent boundary conditions. -/
theorem AdamsLongLayerPairing.boundaryCompatible_of_eq_bot
    (P : AdamsLongLayerPairing unit X r hr p q)
    (hp : adamsBoundaries unit X r hr p.1 p.2 = ⊥)
    (hq : adamsBoundaries unit X r hr q.1 q.2 = ⊥) : P.BoundaryCompatible := by
  constructor
  · intro a ha b
    rw [adamsJ_eq_zero_of_boundaries_eq_bot p.1 p.2 hp a ha, map_zero, LinearMap.zero_apply]
    exact Submodule.zero_mem _
  · intro a b hb
    rw [adamsJ_eq_zero_of_boundaries_eq_bot q.1 q.2 hq b hb, map_zero]
    exact Submodule.zero_mem _

end
end KIP126.Classical.Adams
