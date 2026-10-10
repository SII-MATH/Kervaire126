import KIP126.Main.Solution.Computation.LinProgram.Interpretation.Differential.LongLayer.Proofs
import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Sphere.H6.Lifting.Construction.Proofs
import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Sphere.H6.Boundary.FirstDifferential.Proofs

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology
local notation "C₀" => standardFoundation.Spectrum
local notation "H₀" => standardFoundation.hf2
variable [BraidedCategory C₀] [MonoidalPreadditive C₀]
  [∀ Y : C₀, (tensorRight Y).CommShift ℤ]
  [∀ Y : C₀, (tensorRight Y).IsTriangulated]

/-- The long-layer products and their projection squares are now constructed
from the three lower connecting lifts. Four boundary conditions are proved
from the sphere tower. Only the two cross boundary conditions, the relative
boundary identity, and Lin comparisons remain explicit obligations
for those constructed products, not axioms or claims of permanence. -/
theorem computedH6Square_d_two_eq_zero_of_boundaryLifts
    (R : Mod2RingStructure H₀) (B : SphereH6BoundaryLifts H₀) (hB : B.FitsProducts R)
    (hcross : (B.toLongLayerMaps R hB).CrossBoundaryCompatible R)
    (hLin : (B.toLongLayerMaps R hB).LinCompatible R
      (B.toLongLayerMaps_compatible_of_cross R hB hcross))
    (hδ : (B.toLongLayerMaps R hB).RelativeBoundary R
      (B.toLongLayerMaps_compatible_of_cross R hB hcross)) :
    (sphereAdamsData.d 2 (2, 128)).hom computedH6Square = 0 :=
  computedH6Square_d_two_eq_zero_of_longLayer R (B.toLongLayerMaps R hB)
    (B.toLongLayerMaps_compatible_of_cross R hB hcross) hLin hδ

/-- Alternative lower-page criterion: the two local first-differential
product rules provide the remaining descent conditions. The lower lifts,
their relative boundary identity, and Lin product comparisons are still
required; no witness for the local first-differential rules is postulated. -/
theorem computedH6Square_d_two_eq_zero_of_firstCycleProductRule
    (R : Mod2RingStructure H₀) (B : SphereH6BoundaryLifts H₀) (hB : B.FitsProducts R)
    (hfirst : SphereH6FirstCycleProductRule H₀ R)
    (hLin : (B.toLongLayerMaps R hB).LinCompatible R
      (B.toLongLayerMaps_compatible_of_cross R hB
        (hfirst.crossBoundaryCompatible (B.toLongLayerMaps R hB))))
    (hδ : (B.toLongLayerMaps R hB).RelativeBoundary R
      (B.toLongLayerMaps_compatible_of_cross R hB
        (hfirst.crossBoundaryCompatible (B.toLongLayerMaps R hB)))) :
    (sphereAdamsData.d 2 (2, 128)).hom computedH6Square = 0 :=
  computedH6Square_d_two_eq_zero_of_boundaryLifts R B hB
    (hfirst.crossBoundaryCompatible (B.toLongLayerMaps R hB)) hLin hδ

end
end KIP126.Classical.Adams
