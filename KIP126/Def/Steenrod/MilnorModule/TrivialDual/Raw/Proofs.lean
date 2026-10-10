import KIP126.Def.Steenrod.MilnorModule.TrivialDual.Raw.Data

/-! Evaluation on the specified degree-line generator is an isomorphism
of the actual left modules, not an additional choice of coefficient object. -/

namespace KIP126.Steenrod.Milnor.Module

open CategoryTheory MonoidalCategory

theorem trivialDualHom_action (t : ℤ) :
    (steenrod.X ◁ trivialDualHom t) ≫ (trivialAt t).a =
      (dualLeftModule (Ext.trivialAt t)).a ≫ trivialDualHom t := by
  sorry

theorem trivialDualInv_action (t : ℤ) :
    (steenrod.X ◁ trivialDualInv t) ≫ (dualLeftModule (Ext.trivialAt t)).a =
      (trivialAt t).a ≫ trivialDualInv t := by
  sorry

theorem trivialDualHom_inv (t : ℤ) :
    trivialDualHom t ≫ trivialDualInv t = 𝟙 (dualLeftModule (Ext.trivialAt t)).A := by
  sorry

theorem trivialDualInv_hom (t : ℤ) :
    trivialDualInv t ≫ trivialDualHom t = 𝟙 (trivialAt t).A := by
  sorry

end KIP126.Steenrod.Milnor.Module
