import KIP126.Def.ClassicalAdams.Moss.Composition.LongLayer.Data
import KIP126.Def.ClassicalAdams.TowerLongLayer.One.Proofs
import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Mixed.Data

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

/-- At length one, invert the actual output projection to lift the fixed
coefficient-induced composition. There is no freely chosen long-layer map. -/
def longLayerOneComposition (X Y Z : C) (s t : ℕ) :
    adamsLongLayer H.unit (mappingObject X Y) 1 le_rfl s ⊗
      adamsLongLayer H.unit (mappingObject Y Z) 1 le_rfl t ⟶
        adamsLongLayer H.unit (mappingObject X Z) 1 le_rfl ((s : ℤ) + (t : ℤ)) :=
  longLayerProjectedComposition H R X Y Z 1 le_rfl s t ≫
    inv (adamsLongLayerProjection H.unit (mappingObject X Z) 1 le_rfl
      ((s : ℤ) + (t : ℤ)))

/-- A concrete application of the mixed descent input to the three mapping
objects, with both representative operations constructed from actual maps. -/
def longLayerOnePairing [MonoidalPreadditive C]
    (X Y Z : C) (s t : ℕ) (u v : ℤ) :
    MixedAdamsLongLayerPairing H.unit (mappingObject X Y) (mappingObject Y Z)
      (mappingObject X Z) 1 le_rfl ((s : ℤ), u) ((t : ℤ), v) where
  first := firstComposition H R X Y Z s t u v
  long := homotopyTensorPairing (u - s) (v - t)
    ((u + v) - ((s : ℤ) + (t : ℤ))) (by omega)
      (longLayerOneComposition H R X Y Z s t)

end
end KIP126.Classical.Adams.Moss
