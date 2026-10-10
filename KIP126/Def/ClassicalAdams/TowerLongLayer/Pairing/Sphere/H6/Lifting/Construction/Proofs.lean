import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Sphere.H6.Lifting.Construction.Data
import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Sphere.Lifting.Construction.Proofs
import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Sphere.H6.Predicates
import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Sphere.H6.Boundary.Proofs

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [BraidedCategory C]
  {H : Mod2EilenbergMacLane (C := C)} (B : SphereH6BoundaryLifts H)
  (R : Mod2RingStructure H)
  [∀ Y : C, (tensorRight Y).CommShift ℤ]
  [∀ Y : C, (tensorRight Y).IsTriangulated]
  (h : B.FitsProducts R)

/-- All three constructed spectrum maps retain the supplied connecting maps. -/
theorem SphereH6BoundaryLifts.toLongLayerMaps_boundaries :
    (B.toLongLayerMaps R h).square ≫ HasFunctorialCofiber.cofibδ
      (adamsTowerMapAt H.unit (𝟙_ C) 2 4 (by decide)) = B.square ∧
    (B.toLongLayerMaps R h).left ≫ HasFunctorialCofiber.cofibδ
      (adamsTowerMapAt H.unit (𝟙_ C) 4 6 (by decide)) = B.left ∧
    (B.toLongLayerMaps R h).right ≫ HasFunctorialCofiber.cofibδ
      (adamsTowerMapAt H.unit (𝟙_ C) 4 6 (by decide)) = B.right :=
  ⟨adamsSphereLongLayerProductOfBoundaryLift_boundary H R 2 (by decide) 1 1 B.square h.square,
    adamsSphereLongLayerProductOfBoundaryLift_boundary H R 2 (by decide) 3 1 B.left h.left,
    adamsSphereLongLayerProductOfBoundaryLift_boundary H R 2 (by decide) 1 3 B.right h.right⟩

/-- Projection compatibility is proved by the construction; only the
two-sided tower-kernel boundary conditions remain as descent inputs. -/
theorem SphereH6BoundaryLifts.toLongLayerMaps_compatible [MonoidalPreadditive C]
    (hs : ((B.toLongLayerMaps R h).squarePairing R).BoundaryCompatible)
    (hl : ((B.toLongLayerMaps R h).leftPairing R).BoundaryCompatible)
    (hr : ((B.toLongLayerMaps R h).rightPairing R).BoundaryCompatible) :
    (B.toLongLayerMaps R h).Compatible R where
  square_projection :=
    adamsSphereLongLayerProductOfBoundaryLift_projection H R 2 (by decide) 1 1 B.square h.square
  left_projection :=
    adamsSphereLongLayerProductOfBoundaryLift_projection H R 2 (by decide) 3 1 B.left h.left
  right_projection :=
    adamsSphereLongLayerProductOfBoundaryLift_projection H R 2 (by decide) 1 3 B.right h.right
  square_boundary := hs
  left_boundary := hl
  right_boundary := hr

/-- Four of the six boundary conditions follow from the actual sphere
tower. The two cross conditions suffice for the constructed products. -/
theorem SphereH6BoundaryLifts.toLongLayerMaps_compatible_of_cross [MonoidalPreadditive C]
    (hcross : (B.toLongLayerMaps R h).CrossBoundaryCompatible R) :
    (B.toLongLayerMaps R h).Compatible R :=
  B.toLongLayerMaps_compatible R h ((B.toLongLayerMaps R h).square_boundary R)
    hcross.left_boundary hcross.right_boundary

end
end KIP126.Classical.Adams
