import KIP126.Def.ClassicalAdams.Moss.Composition.LongLayer.Two.Vanishing.Proofs
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
  [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]
  [(mod2UnitNatTrans H).CommShift ℤ]

/-- Choose an actual length-two lift of the specified projected composition,
whose existence has been proved from the ring and triangle structures.
No uniqueness or compatibility between choices at different levels is asserted. -/
def longLayerTwoComposition (X Y Z : C) (s t : ℕ) :
    adamsLongLayer H.unit (mappingObject X Y) 2 (by decide) s ⊗
      adamsLongLayer H.unit (mappingObject Y Z) 2 (by decide) t ⟶
        adamsLongLayer H.unit (mappingObject X Z) 2 (by decide) ((s : ℤ) + (t : ℤ)) :=
  (longLayerTwoComposition_exists H R X Y Z s t).choose

/-- The mixed pairing on the actual three mapping objects. Its first-layer
operation is the fixed coefficient-induced composition; its long operation
comes from the proved length-two lift. -/
def longLayerTwoPairing [MonoidalPreadditive C]
    (X Y Z : C) (s t : ℕ) (u v : ℤ) :
    MixedAdamsLongLayerPairing H.unit (mappingObject X Y) (mappingObject Y Z)
      (mappingObject X Z) 2 (by decide) ((s : ℤ), u) ((t : ℤ), v) where
  first := firstComposition H R X Y Z s t u v
  long := homotopyTensorPairing (u - s) (v - t)
    ((u + v) - ((s : ℤ) + (t : ℤ))) (by omega)
      (longLayerTwoComposition H R X Y Z s t)

end
end KIP126.Classical.Adams.Moss
