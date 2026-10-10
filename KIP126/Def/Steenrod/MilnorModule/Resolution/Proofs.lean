import KIP126.Def.Steenrod.MilnorModule.Resolution.Data

/-! The terms and differentials of the resolution are definitionally the
specified duals. The augmentation is the specified transpose followed by
the actual coefficient evaluation map. -/

namespace KIP126.Steenrod.Milnor.Module

open CategoryTheory

theorem dualCobarResolution_term (R : Ext.CobarResolution) (s : ℕ) :
    (dualCobarResolution R).complex.X s =
      dualLeftModule (R.resolution.cocomplex.X s) := rfl

theorem dualCobarResolution_d (R : Ext.CobarResolution) (i j : ℕ) :
    (dualCobarResolution R).complex.d i j =
      dualLeftMap (R.resolution.cocomplex.d j i) := rfl

theorem dualCobarResolution_augmentation (R : Ext.CobarResolution) :
    (dualCobarResolution R).π.f 0 =
      dualLeftMap (R.resolution.ι.f 0) ≫ (trivialDualIso 0).hom := by
  exact ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

end KIP126.Steenrod.Milnor.Module
