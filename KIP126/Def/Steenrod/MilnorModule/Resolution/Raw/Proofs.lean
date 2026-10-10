import KIP126.Def.Steenrod.MilnorModule.Resolution.Raw.Data

/-!
Properties of the prescribed dual maps. Projectivity is asserted only for
the terms identified with this fixed normalized Milnor cofree resolution;
there is no claim that every injective comodule has a projective dual.
-/

namespace KIP126.Steenrod.Milnor.Module

open CategoryTheory

theorem dualCobarDifferential_shape (R : Ext.CobarResolution) (i j : ℕ)
    (h : ¬ (ComplexShape.down ℕ).Rel i j) :
    dualCobarDifferential R i j = 0 := by
  sorry

theorem dualCobarDifferential_comp (R : Ext.CobarResolution) (i j k : ℕ) :
    dualCobarDifferential R i j ≫ dualCobarDifferential R j k = 0 := by
  sorry

theorem dualCobarDifferential_augmentation (R : Ext.CobarResolution) :
    dualCobarDifferential R 1 0 ≫ dualCobarAugmentationZero R = 0 := by
  sorry

/-- Projectivity of these actual dual normalized-cofree terms, in the full
category of graded left modules over the fixed convolution algebra. -/
theorem dualCobarTerm_projective (R : Ext.CobarResolution) (s : ℕ) :
    Projective (dualCobarTerm R s) := by
  sorry

end KIP126.Steenrod.Milnor.Module
