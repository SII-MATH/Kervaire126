import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Sphere.H6.Data

namespace KIP126.Classical.Adams

open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C] [HasFunctorialCofiber (C := C)]

/-- Lower input for the three h₆-square products: maps to suspended tower
stages, before choosing any product into a long cofiber. No differential
vanishing, multiplication compatibility, or existence assertion is a field. -/
structure SphereH6BoundaryLifts (H : Mod2EilenbergMacLane (C := C)) where
  square : adamsLongLayer H.unit (𝟙_ C) 2 (by decide) 1 ⊗
    adamsLongLayer H.unit (𝟙_ C) 2 (by decide) 1 ⟶
      (adamsTowerAt H.unit (𝟙_ C) 4)⟦(1 : ℤ)⟧
  left : adamsLongLayer H.unit (𝟙_ C) 2 (by decide) 3 ⊗
    adamsLongLayer H.unit (𝟙_ C) 2 (by decide) 1 ⟶
      (adamsTowerAt H.unit (𝟙_ C) 6)⟦(1 : ℤ)⟧
  right : adamsLongLayer H.unit (𝟙_ C) 2 (by decide) 1 ⊗
    adamsLongLayer H.unit (𝟙_ C) 2 (by decide) 3 ⟶
      (adamsTowerAt H.unit (𝟙_ C) 6)⟦(1 : ℤ)⟧

end KIP126.Classical.Adams
