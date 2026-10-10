import KIP126.Def.Steenrod.MilnorExt.Data
import KIP126.Def.Algebra.GradedComodule.Ext.Multiplication.Data

/-!
Yoneda multiplication on the derived Ext of the fixed Milnor coalgebra.
The operation is derived-category composition after the actual internal
shift; comparison with cobar concatenation is a separate property.
-/

namespace KIP126.Steenrod.Milnor.Ext

open KIP126.Core.Algebra KIP126.Algebra.GradedComodule

/-- The actual bigraded Yoneda product on sphere coefficient Ext. -/
noncomputable def yoneda {s s' : ℕ} {t t' : ℤ} :
    SphereExt s t →ₗ[F2] SphereExt s' t' →ₗ[F2]
      SphereExt (s + s') (t + t') :=
  coefficientYoneda Coalgebra.coaugmentation s s' t t'

end KIP126.Steenrod.Milnor.Ext
