import KIP126.Def.Steenrod.MilnorModule.Data
import KIP126.Def.Algebra.GradedModule.Ext.Multiplication.Proofs

/-!
# Actual Yoneda multiplication in the fixed left Steenrod-module model

The operation uses the actual internal shift and derived composition of
left modules.  Its agreement with cobar concatenation or right-comodule
Yoneda multiplication is a separate comparison property.
-/

namespace KIP126.Steenrod.Milnor.Module

open KIP126.Core.Algebra KIP126.Algebra.GradedModule

/-- The bigraded product on actual left-module sphere Ext. -/
noncomputable def yoneda {s s' : ℕ} {t t' : ℤ} :
    SphereExt s t →ₗ[F2] SphereExt s' t' →ₗ[F2]
      SphereExt (s + s') (t + t') :=
  coefficientYoneda augmentation s s' t t'

end KIP126.Steenrod.Milnor.Module
