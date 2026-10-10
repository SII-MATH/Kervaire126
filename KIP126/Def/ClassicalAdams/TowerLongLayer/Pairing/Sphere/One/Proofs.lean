import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Sphere.One.Data
import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Sphere.Proofs
import KIP126.Def.ClassicalAdams.TowerLayer.Basic.Proofs

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]

/-- At the first page there are no boundaries, so any bilinear representative
pairing satisfies the boundary condition. This does not prove a Leibniz rule. -/
theorem AdamsLongLayerPairing.boundaryCompatible_one
    {H : C} {unit : 𝟙_ C ⟶ H} {X : C} {p q : ℤ × ℤ}
    (P : AdamsLongLayerPairing unit X 1 le_rfl p q) : P.BoundaryCompatible := by
  constructor
  · intro a ha b
    have hz : adamsJ unit X p.1 p.2 a = 0 := by
      have hb : adamsJ unit X p.1 p.2 a ∈ adamsBoundaries unit X 1 le_rfl p.1 p.2 :=
        ⟨a, ha, rfl⟩
      simpa only [adamsBoundaries_one, Submodule.mem_bot] using hb
    rw [hz, map_zero, LinearMap.zero_apply]
    exact Submodule.zero_mem _
  · intro a b hb
    have hz : adamsJ unit X q.1 q.2 b = 0 := by
      have hc : adamsJ unit X q.1 q.2 b ∈ adamsBoundaries unit X 1 le_rfl q.1 q.2 :=
        ⟨b, hb, rfl⟩
      simpa only [adamsBoundaries_one, Submodule.mem_bot] using hc
    rw [hz, map_zero]
    exact Submodule.zero_mem _

variable [BraidedCategory C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  [∀ Y : C, (tensorRight Y).CommShift ℤ]
  [∀ Y : C, (tensorRight Y).IsTriangulated]

omit [MonoidalPreadditive C] in
theorem adamsSphereLongLayerOneProduct_projection (s t : ℕ) :
    adamsSphereLongLayerOneProduct H R s t ≫
      adamsLongLayerProjection H.unit (𝟙_ C) 1 le_rfl ((s : ℤ) + (t : ℤ)) =
        (adamsLongLayerProjection H.unit (𝟙_ C) 1 le_rfl s ⊗ₘ
          adamsLongLayerProjection H.unit (𝟙_ C) 1 le_rfl t) ≫
            adamsSphereLayerProductOrdered H R s t := by
  simp [adamsSphereLongLayerOneProduct]

theorem adamsSphereLongLayerOnePairing_projection (s t : ℕ) (u v : ℤ) :
    (adamsSphereLongLayerOnePairing H R s t u v).ProjectionCompatible :=
  adamsSphereLongLayerPairing_projection H R 1 le_rfl s t u v _
    (adamsSphereLongLayerOneProduct_projection H R s t)

end
end KIP126.Classical.Adams
