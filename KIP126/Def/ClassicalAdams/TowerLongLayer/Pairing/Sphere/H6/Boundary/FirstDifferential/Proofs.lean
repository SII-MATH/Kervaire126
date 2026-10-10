import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Sphere.H6.Boundary.FirstDifferential.Predicates
import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Sphere.H6.Boundary.Proofs
import KIP126.Def.ClassicalAdams.TowerLayer.FirstBoundary.Proofs

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [BraidedCategory C] [MonoidalPreadditive C]
  {H : Mod2EilenbergMacLane (C := C)} {R : Mod2RingStructure H}
  [∀ Y : C, (tensorRight Y).CommShift ℤ]
  [∀ Y : C, (tensorRight Y).IsTriangulated]

/-- The two concrete d₁ identities imply all remaining cross boundary
conditions. This is independent of which long-layer maps were chosen. -/
theorem SphereH6FirstCycleProductRule.crossBoundaryCompatible
    (h : SphereH6FirstCycleProductRule H R) (M : SphereH6LongLayerMaps H) :
    M.CrossBoundaryCompatible R := by
  constructor
  · intro a ha b
    let z := adamsJToCycles H.unit (𝟙_ C) 2 (by decide) 3 65 a
    have hz : z.val ∈ adamsBoundaries H.unit (𝟙_ C) 2 (by decide) 3 65 := ⟨a, ha, rfl⟩
    obtain ⟨y, hy⟩ := adamsBoundary_two_exists_first_primitive H.unit (𝟙_ C) 2 65 z hz
    let b' := adamsLongLayerToCycles H.unit (𝟙_ C) 2 (by decide) 1 64 b
    have hb := adamsPageOneEquiv_d_mem_boundaries H.unit (𝟙_ C) 3 129
      (adamsSpherePageOneProduct H R 2 1 65 64 y
        (adamsNextCycleToPage H.unit (𝟙_ C) 1 le_rfl 1 64 b'))
    have he := h.left y b'
    simp only [Int.reduceAdd, Int.reduceSub] at hy hb
    erw [hy] at he
    erw [he] at hb
    exact hb
  · intro a b hb
    let z := adamsJToCycles H.unit (𝟙_ C) 2 (by decide) 3 65 b
    have hz : z.val ∈ adamsBoundaries H.unit (𝟙_ C) 2 (by decide) 3 65 := ⟨b, hb, rfl⟩
    obtain ⟨y, hy⟩ := adamsBoundary_two_exists_first_primitive H.unit (𝟙_ C) 2 65 z hz
    let a' := adamsLongLayerToCycles H.unit (𝟙_ C) 2 (by decide) 1 64 a
    have ha := adamsPageOneEquiv_d_mem_boundaries H.unit (𝟙_ C) 3 129
      (adamsSpherePageOneProduct H R 1 2 64 65
        (adamsNextCycleToPage H.unit (𝟙_ C) 1 le_rfl 1 64 a') y)
    have he := h.right a' y
    simp only [Int.reduceAdd, Int.reduceSub] at hy ha
    erw [hy] at he
    erw [he] at ha
    exact ha

end
end KIP126.Classical.Adams
