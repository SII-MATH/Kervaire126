import KIP126.Def.ClassicalAdams.Moss.Composition.LongLayer.Two.Pairing.Proofs
import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Mixed.Cycles.Data

namespace KIP126.Classical.Adams.Moss

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [MonoidalClosed C] [BraidedCategory C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  [∀ A : C, (tensorRight A).CommShift ℤ]
  [∀ A : C, (tensorRight A).IsTriangulated]
  [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]
  [(mod2UnitNatTrans H).CommShift ℤ] [MonoidalPreadditive C]

/-- Actual composition on the second-page cycle modules of the three mapping
objects. Its underlying operation is the fixed first-layer composition.
This is not yet a pairing on the internal E₂ boundary quotient. -/
def twoCycleComposition (X Y Z : C) (s t : ℕ) (u v : ℤ) :
    adamsCycles H.unit (mappingObject X Y) 2 (by decide) s u →ₗ[ℤ]
      adamsCycles H.unit (mappingObject Y Z) 2 (by decide) t v →ₗ[ℤ]
        adamsCycles H.unit (mappingObject X Z) 2 (by decide) ((s : ℤ) + (t : ℤ)) (u + v) :=
  (longLayerTwoPairing H R X Y Z s t u v).onCycles
    (longLayerTwoPairing_projection H R X Y Z s t u v)

end
end KIP126.Classical.Adams.Moss
