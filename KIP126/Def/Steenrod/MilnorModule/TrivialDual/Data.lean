import KIP126.Def.Steenrod.MilnorModule.TrivialDual.Raw.Proofs

/-! The dual of the actual trivial right comodule is the actual trivial
left module in the same degree, via the explicit evaluation isomorphism. -/

namespace KIP126.Steenrod.Milnor.Module

open CategoryTheory

/-- The fixed coefficient identification for contravariant dualization. -/
noncomputable def trivialDualIso (t : ℤ) : dualLeftModule (Ext.trivialAt t) ≅ trivialAt t where
  hom := ⟨trivialDualHom t, trivialDualHom_action t⟩
  inv := ⟨trivialDualInv t, trivialDualInv_action t⟩
  hom_inv_id := Monad.Algebra.Hom.ext (trivialDualHom_inv t)
  inv_hom_id := Monad.Algebra.Hom.ext (trivialDualInv_hom t)

end KIP126.Steenrod.Milnor.Module
