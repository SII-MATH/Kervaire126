import KIP126.Def.Steenrod.MilnorModule.Resolution.Complex.Data

/-! Exactness of this actual augmented dual complex remains a proof
obligation. It is not deduced from an unrestricted categorical duality. -/

namespace KIP126.Steenrod.Milnor.Module

open CategoryTheory

theorem dualCobarAugmentation_quasiIso (R : Ext.CobarResolution) :
    QuasiIso (dualCobarAugmentation R) := by
  sorry

end KIP126.Steenrod.Milnor.Module
