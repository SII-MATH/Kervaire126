import KIP126.Def.Steenrod.MilnorExt.Cofree.Data

/-! The prescribed polynomial coordinates do not forget comodule elements. -/

namespace KIP126.Steenrod.Milnor.Ext.Cofree

/-- Disjoint slot monomials and the Cauchy degree decomposition identify the
cofree term with its polynomial image; there is no coordinate quotient here. -/
theorem termPolynomial_injective (s : ℕ) (n : ℤ) :
    Function.Injective (termPolynomial s n) := by
  sorry

end KIP126.Steenrod.Milnor.Ext.Cofree
