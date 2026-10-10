import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Sphere.Data

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]

/-- The three actual two-step layer maps needed for the square and its two
second-differential terms. This record neither postulates their existence nor
contains a page differential or a survival assertion. -/
structure SphereH6LongLayerMaps (H : Mod2EilenbergMacLane (C := C)) where
  square : adamsLongLayer H.unit (𝟙_ C) 2 (by decide) 1 ⊗
    adamsLongLayer H.unit (𝟙_ C) 2 (by decide) 1 ⟶
      adamsLongLayer H.unit (𝟙_ C) 2 (by decide) 2
  left : adamsLongLayer H.unit (𝟙_ C) 2 (by decide) 3 ⊗
    adamsLongLayer H.unit (𝟙_ C) 2 (by decide) 1 ⟶
      adamsLongLayer H.unit (𝟙_ C) 2 (by decide) 4
  right : adamsLongLayer H.unit (𝟙_ C) 2 (by decide) 1 ⊗
    adamsLongLayer H.unit (𝟙_ C) 2 (by decide) 3 ⟶
      adamsLongLayer H.unit (𝟙_ C) 2 (by decide) 4

variable [BraidedCategory C] [MonoidalPreadditive C]
  {H : Mod2EilenbergMacLane (C := C)} (M : SphereH6LongLayerMaps H)
  (R : Mod2RingStructure H)
  [∀ Y : C, (tensorRight Y).CommShift ℤ]
  [∀ Y : C, (tensorRight Y).IsTriangulated]

def SphereH6LongLayerMaps.squarePairing :
    AdamsLongLayerPairing H.unit (𝟙_ C) 2 (by decide) (1, 64) (1, 64) :=
  adamsSphereLongLayerPairing H R 2 (by decide) 1 1 64 64 M.square

def SphereH6LongLayerMaps.leftPairing :
    AdamsLongLayerPairing H.unit (𝟙_ C) 2 (by decide) (3, 65) (1, 64) :=
  adamsSphereLongLayerPairing H R 2 (by decide) 3 1 65 64 M.left

def SphereH6LongLayerMaps.rightPairing :
    AdamsLongLayerPairing H.unit (𝟙_ C) 2 (by decide) (1, 64) (3, 65) :=
  adamsSphereLongLayerPairing H R 2 (by decide) 1 3 64 65 M.right

end
end KIP126.Classical.Adams
