import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Sphere.Lifting.Construction.Proofs
import KIP126.Def.ClassicalAdams.TowerLongLayer.Boundary.Proofs
import KIP126.Def.StableHomotopy.Context.Connecting.Desuspension.Proofs

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [BraidedCategory C] [MonoidalPreadditive C]
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
  (u v : ℤ)
  (a : HomotopyGroup (u - s) (adamsLongLayer H.unit (𝟙_ C) r hr s))
  (b : HomotopyGroup (v - t) (adamsLongLayer H.unit (𝟙_ C) r hr t))

/-- The constructed product's long connecting class is computed by the
supplied spectrum-level lift itself, not by an unspecified choice of product. -/
theorem adamsSphereLongLayerProductOfBoundaryLift_K :
    adamsLongLayerK H.unit (𝟙_ C) r hr ((s : ℤ) + (t : ℤ)) (u + v)
      (homotopyTensorPairing (u - s) (v - t) ((u + v) - ((s : ℤ) + (t : ℤ)))
        (by omega) (adamsSphereLongLayerProductOfBoundaryLift H R r hr s t y hy) a b) =
      homotopyDesuspend (adamsTowerAt H.unit (𝟙_ C) (((s : ℤ) + (t : ℤ)) + r))
        ((u + v) - ((s : ℤ) + (t : ℤ)))
        (homotopyTensorPairing (u - s) (v - t) ((u + v) - ((s : ℤ) + (t : ℤ)))
          (by omega) y a b) := by
  have hc := connectingHomomorphism_eq_desuspend
    (HoCofiberSequence.ofMorphism (adamsTowerMapAt H.unit (𝟙_ C)
      ((s : ℤ) + (t : ℤ)) (((s : ℤ) + (t : ℤ)) + r) (by omega)))
    ((u + v) - ((s : ℤ) + (t : ℤ)))
    (homotopyTensorPairing (u - s) (v - t) ((u + v) - ((s : ℤ) + (t : ℤ)))
      (by omega) (adamsSphereLongLayerProductOfBoundaryLift H R r hr s t y hy) a b)
  have hb : homotopyTensorPairing (u - s) (v - t) ((u + v) - ((s : ℤ) + (t : ℤ)))
      (by omega) (adamsSphereLongLayerProductOfBoundaryLift H R r hr s t y hy) a b ≫
      HasFunctorialCofiber.cofibδ (adamsTowerMapAt H.unit (𝟙_ C)
        ((s : ℤ) + (t : ℤ)) (((s : ℤ) + (t : ℤ)) + r) (by omega)) =
      homotopyTensorPairing (u - s) (v - t) ((u + v) - ((s : ℤ) + (t : ℤ)))
        (by omega) y a b := by
    simp only [homotopyTensorPairing, tensorHomPairing_apply, Category.assoc,
      adamsSphereLongLayerProductOfBoundaryLift_boundary]
  exact hc.trans (congrArg (homotopyDesuspend
    (adamsTowerAt H.unit (𝟙_ C) (((s : ℤ) + (t : ℤ)) + r))
    ((u + v) - ((s : ℤ) + (t : ℤ)))) hb)

/-- The actual page differential of the represented product is `j` applied
to the desuspension of the supplied lift evaluated on the two representatives.
This needs no assumed page derivation law or descended quotient product. -/
theorem adamsSphereLongLayerProductOfBoundaryLift_differential :
    adamsDifferential H.unit (𝟙_ C) r hr ((s : ℤ) + (t : ℤ)) (u + v)
      (adamsLongLayerToPage H.unit (𝟙_ C) r hr ((s : ℤ) + (t : ℤ)) (u + v)
        (homotopyTensorPairing (u - s) (v - t) ((u + v) - ((s : ℤ) + (t : ℤ)))
          (by omega) (adamsSphereLongLayerProductOfBoundaryLift H R r hr s t y hy) a b)) =
      adamsJToPage H.unit (𝟙_ C) r hr (((s : ℤ) + (t : ℤ)) + r) ((u + v) + r - 1)
        (Eq.mp (congrArg (fun k => HomotopyGroup k
          (adamsTowerAt H.unit (𝟙_ C) (((s : ℤ) + (t : ℤ)) + r)))
          (by omega : (u + v) - ((s : ℤ) + (t : ℤ)) - 1 =
            ((u + v) + r - 1) - (((s : ℤ) + (t : ℤ)) + r)))
          (homotopyDesuspend (adamsTowerAt H.unit (𝟙_ C) (((s : ℤ) + (t : ℤ)) + r))
            ((u + v) - ((s : ℤ) + (t : ℤ)))
            (homotopyTensorPairing (u - s) (v - t) ((u + v) - ((s : ℤ) + (t : ℤ)))
              (by omega) y a b))) := by
  have hd := adamsDifferential_longLayerToPage H.unit (𝟙_ C) r hr
    ((s : ℤ) + (t : ℤ)) (u + v)
    (homotopyTensorPairing (u - s) (v - t) ((u + v) - ((s : ℤ) + (t : ℤ)))
      (by omega) (adamsSphereLongLayerProductOfBoundaryLift H R r hr s t y hy) a b)
  rw [adamsSphereLongLayerProductOfBoundaryLift_K H R r hr s t y hy u v a b] at hd
  exact hd

end
end KIP126.Classical.Adams
