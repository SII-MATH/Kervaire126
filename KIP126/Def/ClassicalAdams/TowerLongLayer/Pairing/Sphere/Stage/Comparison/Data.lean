module

public import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Sphere.Stage.Data
public import KIP126.Def.ClassicalAdams.TowerSmash.Pairing.Layer.Multiplication.Data

@[expose] public section


/-! The two existing geometric constructions compared in this module:
the chosen long-layer/stage triangle map projected to the first layer, and
the specified coefficient product after the source projections. No new
triangle completion or compatibility hypothesis is introduced. -/

namespace KIP126.Classical.Adams.LongLayerStageComparison
noncomputable section
open CategoryTheory MonoidalCategory Pretriangulated KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]

/-- The same long-cofiber projection with natural-number endpoints exposed.
The companion theorem identifies it with `adamsLongLayerProjection`. -/
def projectionNat {U : C} (unit : 𝟙_ C ⟶ U) (X : C)
    (s n : ℕ) (h : s + 1 ≤ n) :
    HasFunctorialCofiber.cofib (adamsTowerMap unit X s n (by omega)) ⟶
      adamsLayerAt unit X s := by
  change _ ⟶ HasFunctorialCofiber.cofib (adamsTowerMap unit X s (s + 1) (by omega))
  exact cofiberFactorizationMap _ _ (adamsTowerMap unit X (s + 1) n h)
    (adamsTowerMap_comp unit X s (s + 1) n (by omega) h)

variable [∀ Y : C, (tensorRight Y).CommShift ℤ]
  [∀ Y : C, (tensorRight Y).IsTriangulated]

/-- Project the already chosen arbitrary-length stage pairing. No second
completion of a triangle is selected here. -/
def stageProjected [MonoidalPreadditive C] {U : C} (unit : 𝟙_ C ⟶ U)
    (r : ℕ) (hr : 1 ≤ r) (s t : ℕ) :
    HasFunctorialCofiber.cofib (adamsTowerMap unit (𝟙_ C) s (s + r) (by omega)) ⊗
      adamsTower unit (𝟙_ C) t ⟶ adamsLayerAt unit (𝟙_ C) ((t + s : ℕ) : ℤ) :=
  (adamsSphereLongLayerStageTriangleIso unit r s t).hom.hom₃ ≫
    projectionNat unit (𝟙_ C) (t + s) (t + (s + r)) (by omega)

/-- The coefficient product restricted along the actual long projection and
actual tower-to-layer inclusion. Its value does not use a chosen stage map. -/
def coefficientAction [BraidedCategory C]
    (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
    (r : ℕ) (hr : 1 ≤ r) (s t : ℕ) :
    HasFunctorialCofiber.cofib (adamsTowerMap H.unit (𝟙_ C) s (s + r) (by omega)) ⊗
      adamsTower H.unit (𝟙_ C) t ⟶ adamsLayerAt H.unit (𝟙_ C) ((t + s : ℕ) : ℤ) :=
  (projectionNat H.unit (𝟙_ C) s (s + r) (by omega) ⊗ₘ
    (adamsLayerTriangle H.unit (𝟙_ C) t).mor₂) ≫ adamsSphereLayerProduct H R s t

end
end KIP126.Classical.Adams.LongLayerStageComparison
