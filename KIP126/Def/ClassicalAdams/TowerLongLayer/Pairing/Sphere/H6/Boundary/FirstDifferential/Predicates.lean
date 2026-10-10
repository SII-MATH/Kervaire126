import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Sphere.One.Page.Data
import KIP126.Def.ClassicalAdams.TowerLayer.Data
import KIP126.Def.ClassicalAdams.TowerSequence.NextCycles.Data

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

/-- Two local first-differential product rules, with the other input an
actual second-cycle representative. All products and differentials are the
ones already constructed from the tower. No long-layer product, E₂ product,
Lin comparison, or d₂ value is an input to this predicate.
The unsigned form is intended for the mod-two pages. -/
structure SphereH6FirstCycleProductRule : Prop where
  left : ∀ (a : adamsPage H.unit (𝟙_ C) 1 le_rfl 2 65)
    (b : adamsCycles H.unit (𝟙_ C) 2 (by decide) 1 64),
    adamsPageOneEquiv H.unit (𝟙_ C) 4 129
      ((adamsPageD H.unit (𝟙_ C) 1 le_rfl (3, 129) (4, 129)).hom
        (adamsSpherePageOneProduct H R 2 1 65 64 a
          (adamsNextCycleToPage H.unit (𝟙_ C) 1 le_rfl 1 64 b))) =
      adamsSphereE1Product H R 3 1 65 64
        (adamsPageOneEquiv H.unit (𝟙_ C) 3 65
          ((adamsPageD H.unit (𝟙_ C) 1 le_rfl (2, 65) (3, 65)).hom a)) b.val
  right : ∀ (a : adamsCycles H.unit (𝟙_ C) 2 (by decide) 1 64)
    (b : adamsPage H.unit (𝟙_ C) 1 le_rfl 2 65),
    adamsPageOneEquiv H.unit (𝟙_ C) 4 129
      ((adamsPageD H.unit (𝟙_ C) 1 le_rfl (3, 129) (4, 129)).hom
        (adamsSpherePageOneProduct H R 1 2 64 65
          (adamsNextCycleToPage H.unit (𝟙_ C) 1 le_rfl 1 64 a) b)) =
      adamsSphereE1Product H R 1 3 64 65 a.val
        (adamsPageOneEquiv H.unit (𝟙_ C) 3 65
          ((adamsPageD H.unit (𝟙_ C) 1 le_rfl (2, 65) (3, 65)).hom b))

end
end KIP126.Classical.Adams
