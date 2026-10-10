import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Sphere.Lifting.Construction.Data
import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Sphere.Proofs

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
  (r : ℕ) (hr : 1 ≤ r) (s t : ℕ)
  (y : adamsLongLayer H.unit (𝟙_ C) r hr s ⊗
    adamsLongLayer H.unit (𝟙_ C) r hr t ⟶
      (adamsTowerAt H.unit (𝟙_ C) (((s : ℤ) + (t : ℤ)) + r))⟦(1 : ℤ)⟧)
  (hy : y ≫ (adamsTowerMapAt H.unit (𝟙_ C) (((s : ℤ) + (t : ℤ)) + 1)
    (((s : ℤ) + (t : ℤ)) + r) (by omega))⟦(1 : ℤ)⟧' =
      adamsSphereLongLayerProductBoundary H R r hr s t)

theorem adamsSphereLongLayerProductOfBoundaryLift_projection :
    adamsSphereLongLayerProductOfBoundaryLift H R r hr s t y hy ≫
      adamsLongLayerProjection H.unit (𝟙_ C) r hr ((s : ℤ) + (t : ℤ)) =
        adamsSphereLongLayerProjectedProduct H R r hr s t :=
  (Classical.choose_spec (adamsSphereLongLayerProduct_exists_of_boundaryLift H R r hr s t y hy)).1

/-- Unlike an arbitrary choice of a projection lift, this constructed map
has exactly the connecting morphism supplied as input. -/
theorem adamsSphereLongLayerProductOfBoundaryLift_boundary :
    adamsSphereLongLayerProductOfBoundaryLift H R r hr s t y hy ≫
      HasFunctorialCofiber.cofibδ
        (adamsTowerMapAt H.unit (𝟙_ C) ((s : ℤ) + (t : ℤ))
          (((s : ℤ) + (t : ℤ)) + r) (by omega)) = y :=
  (Classical.choose_spec (adamsSphereLongLayerProduct_exists_of_boundaryLift H R r hr s t y hy)).2

/-- Every bidegree specialization of the constructed spectrum product
automatically has the required representative projection compatibility. -/
theorem adamsSphereLongLayerPairingOfBoundaryLift_projection [MonoidalPreadditive C]
    (u v : ℤ) :
    (adamsSphereLongLayerPairing H R r hr s t u v
      (adamsSphereLongLayerProductOfBoundaryLift H R r hr s t y hy)).ProjectionCompatible :=
  adamsSphereLongLayerPairing_projection H R r hr s t u v _
    (adamsSphereLongLayerProductOfBoundaryLift_projection H R r hr s t y hy)

end
end KIP126.Classical.Adams
