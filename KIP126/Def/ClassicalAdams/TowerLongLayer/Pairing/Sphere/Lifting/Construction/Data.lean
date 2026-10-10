import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Sphere.Lifting.Proofs

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [BraidedCategory C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  [∀ Y : C, (tensorRight Y).CommShift ℤ]
  [∀ Y : C, (tensorRight Y).IsTriangulated]

/-- Choose an actual long-layer product from a lift of the prescribed
connecting map, retaining that connecting map. Existence follows from
exactness, not a new axiom. No two-term boundary identity, higher coherence,
or Lin compatibility is asserted by this choice. -/
def adamsSphereLongLayerProductOfBoundaryLift (r : ℕ) (hr : 1 ≤ r) (s t : ℕ)
    (y : adamsLongLayer H.unit (𝟙_ C) r hr s ⊗
      adamsLongLayer H.unit (𝟙_ C) r hr t ⟶
        (adamsTowerAt H.unit (𝟙_ C) (((s : ℤ) + (t : ℤ)) + r))⟦(1 : ℤ)⟧)
    (hy : y ≫ (adamsTowerMapAt H.unit (𝟙_ C) (((s : ℤ) + (t : ℤ)) + 1)
      (((s : ℤ) + (t : ℤ)) + r) (by omega))⟦(1 : ℤ)⟧' =
        adamsSphereLongLayerProductBoundary H R r hr s t) :
    adamsLongLayer H.unit (𝟙_ C) r hr s ⊗ adamsLongLayer H.unit (𝟙_ C) r hr t ⟶
      adamsLongLayer H.unit (𝟙_ C) r hr ((s : ℤ) + (t : ℤ)) :=
  Classical.choose (adamsSphereLongLayerProduct_exists_of_boundaryLift H R r hr s t y hy)

end
end KIP126.Classical.Adams
