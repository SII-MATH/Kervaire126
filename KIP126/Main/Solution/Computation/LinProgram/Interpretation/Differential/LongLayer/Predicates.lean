import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Sphere.H6.Leibniz.Predicates
import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Internal.Proofs
import KIP126.Main.Solution.Computation.LinProgram.Interpretation.Classes.Data

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology

local notation "C₀" => standardFoundation.Spectrum
local notation "H₀" => standardFoundation.hf2
variable [BraidedCategory C₀] [MonoidalPreadditive C₀]
  [∀ Y : C₀, (tensorRight Y).CommShift ℤ]
  [∀ Y : C₀, (tensorRight Y).IsTriangulated]

/-- Only the three needed products are compared with the fixed Lin
presentation. The products on the left are constructed from the supplied
actual spectrum maps and the specified coefficient multiplication.
This condition supplies no differential and asserts no survival. -/
structure SphereH6LongLayerMaps.LinCompatible
    (M : SphereH6LongLayerMaps H₀) (R : Mod2RingStructure H₀) (h : M.Compatible R) : Prop where
  square : ∀ x y, (M.squarePairing R).onInternalPage h.square h.square_boundary x y =
    linE2Presentation.product 1 64 1 64 x y
  left : ∀ x y, (M.leftPairing R).onInternalPage h.left h.left_boundary x y =
    linE2Presentation.product 3 65 1 64 x y
  right : ∀ x y, (M.rightPairing R).onInternalPage h.right h.right_boundary x y =
    linE2Presentation.product 1 64 3 65 x y

end
end KIP126.Classical.Adams
