import KIP126.Def.Steenrod.MilnorModule.Comparison.Multiplication.Predicates

/-!
# Yoneda and unit laws for the prescribed dual-cobar comparison

The premise is the existing formula on every actual resolution cocycle.
Multiplicativity is a conclusion about derived composition, not an additional
assumption on the comparison.  Proofs require compatibility of the actual
dual resolution with shifts and composition and remain staged separately.
-/

namespace KIP126.Steenrod.Milnor.Module

open KIP126.Core.Algebra

/-- The comparison fixed on every dual-cobar representative preserves the
two actual Yoneda products.  This is the characteristic-two, same-degree
statement for the fixed Steenrod model; it does not generalize away the
contravariant shift signs over other coefficient fields. -/
theorem preservesYoneda_of_preservesDualCobarRepresentatives (R : Ext.CobarResolution)
    {e : ∀ (s : ℕ) (t : ℤ), Ext.SphereExt s t ≃ₗ[F2] SphereExt s t}
    (he : PreservesDualCobarRepresentatives R e) : PreservesYoneda e := by
  sorry

/-- The same representative constraint also preserves the actual identity
class, with the same comparison family and source resolution. -/
theorem preservesUnit_of_preservesDualCobarRepresentatives (R : Ext.CobarResolution)
    {e : ∀ (s : ℕ) (t : ℤ), Ext.SphereExt s t ≃ₗ[F2] SphereExt s t}
    (he : PreservesDualCobarRepresentatives R e) : PreservesUnit e := by
  sorry

end KIP126.Steenrod.Milnor.Module
