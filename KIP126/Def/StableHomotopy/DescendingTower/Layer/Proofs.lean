import KIP126.Def.StableHomotopy.DescendingTower.Layer.Data
import KIP126.Def.StableHomotopy.DescendingTower.Proofs

/-! The chosen layer triangle is distinguished. Its negative-filtration
layers in a constant-tail extension are zero, as a property of those
actual cofibers rather than a replacement of the layer objects. -/

namespace KIP126.StableHomotopy

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

set_option backward.isDefEq.respectTransparency false

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]

theorem DescendingTower.layerTriangle_distinguished (T : DescendingTower C) (k : ℤ) :
    T.layerTriangle k ∈ distTriang C :=
  HasFunctorialCofiber.cofib_distinguished (T.step k)

theorem DescendingTower.step_layerIncl (T : DescendingTower C) (k : ℤ) :
    T.step k ≫ T.layerIncl k = 0 :=
  comp_distTriang_mor_zero₁₂ _ (T.layerTriangle_distinguished k)

theorem DescendingTower.layerIncl_boundary (T : DescendingTower C) (k : ℤ) :
    T.layerIncl k ≫ T.layerBoundary k = 0 :=
  comp_distTriang_mor_zero₂₃ _ (T.layerTriangle_distinguished k)

theorem DescendingTower.layerBoundary_step (T : DescendingTower C) (k : ℤ) :
    T.layerBoundary k ≫ (T.step k)⟦(1 : ℤ)⟧' = 0 :=
  comp_distTriang_mor_zero₃₁ _ (T.layerTriangle_distinguished k)

theorem InverseSequence.toDescendingTower_layer_isZero (D : InverseSequence C)
    (k : ℤ) (hk : k < 0) : IsZero (D.toDescendingTower.layer k) := by
  apply (Triangle.isZero₃_iff_isIso₁ _ (D.toDescendingTower.layerTriangle_distinguished k)).2
  change IsIso (D.toDescendingTower.step k)
  rw [InverseSequence.toDescendingTower_step_neg D k hk]
  infer_instance

end KIP126.StableHomotopy
