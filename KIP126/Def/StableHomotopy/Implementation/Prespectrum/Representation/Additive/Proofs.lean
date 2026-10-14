module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Functor.Product.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

set_option backward.isDefEq.respectTransparency false

/-- The inverse of the original sphere representation is additive for the
actual stable-category addition. -/
theorem sourceStableHomotopyEquiv_symm_add (X : Prespectrum) (d : ℤ)
    (f g : sourceSphere d ⟶ sourceLocalization.obj X) :
    (sourceStableHomotopyEquiv X d).symm (f + g) =
      (sourceStableHomotopyEquiv X d).symm f + (sourceStableHomotopyEquiv X d).symm g := by
  simp only [sourceStableHomotopyEquiv_symm_apply]
  have hf := sourceStableHomotopyAddFunctor_forget_map f d
  have hg := sourceStableHomotopyAddFunctor_forget_map g d
  have hfg := sourceStableHomotopyAddFunctor_forget_map (f + g) d
  rw [← hf, ← hg, ← hfg, Functor.map_add]
  rfl

/-- The original equivalence from cubical stable classes to maps out of the
specified sphere preserves their constructed group additions. -/
theorem sourceStableHomotopyEquiv_add (X : Prespectrum) (d : ℤ)
    (x y : StableHomotopy X d) :
    sourceStableHomotopyEquiv X d (x + y) =
      sourceStableHomotopyEquiv X d x + sourceStableHomotopyEquiv X d y := by
  apply (sourceStableHomotopyEquiv X d).symm.injective
  rw [sourceStableHomotopyEquiv_symm_add]
  simp only [Equiv.symm_apply_apply]

end KIP126.StableHomotopy.Implementation.Prespectrum
