import KIP126.Def.Synthetic.Sphere.Shift.Raw.Data
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
Additivity is a consequence of the existing synthetic background, not a new
model assumption. The composition and zero comparisons make the shift by
`-p` an inverse equivalence to the shift by `p`. A pretriangulated category
has binary biproducts, and equivalences preserve them and zero morphisms;
hence these existing bigraded shift functors are additive. The equivalence
argument is adapted from `KIPBase/Synthetic/Basic.lean` to the existing context.
-/

namespace KIP126.Synthetic.Context

open CategoryTheory

universe u v

variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]

/-- The existing bigraded shift preserves addition. -/
theorem biShift_additive (p : ℤ × ℤ) :
    (SyntheticCategory.biShift (Syn := Syn) p).Additive := by
  letI : (SyntheticCategory.biShift (Syn := Syn) p).IsEquivalence :=
    Functor.IsEquivalence.mk' (SyntheticCategory.biShift (-p))
      (SyntheticCategory.biShift_zero.symm ≪≫
        eqToIso (congrArg SyntheticCategory.biShift
          (by simp : (0 : ℤ × ℤ) = p + -p)) ≪≫
        (SyntheticCategory.biShift_comp p (-p)).symm)
      (SyntheticCategory.biShift_comp (-p) p ≪≫
        eqToIso (congrArg SyntheticCategory.biShift
          (by simp : -p + p = (0 : ℤ × ℤ))) ≪≫
        SyntheticCategory.biShift_zero)
  exact Functor.additive_of_preserves_binary_products _

attribute [instance] biShift_additive

/-- Additivity of the already defined suspension-invariance function. -/
theorem susp_invariance_add (m n k l : ℤ) (X : Syn)
    (f g : BiHom m n X) :
    susp_invariance m n k l X (f + g) =
      susp_invariance m n k l X f + susp_invariance m n k l X g := by
  simp [susp_invariance, Functor.map_add, Preadditive.comp_add]

/-- The specified inverse reindexing map is additive. -/
theorem biSuspensionHomEquivRaw_add (n w q : ℤ) (Q : Syn)
    (f g : BiHom n w (((SyntheticCategory.biShift (0, -q)).obj Q)⟦(1 : ℤ)⟧)) :
    biSuspensionHomEquivRaw n w q Q (f + g) =
      biSuspensionHomEquivRaw n w q Q f + biSuspensionHomEquivRaw n w q Q g := by
  let e := biSuspensionHomEquivRaw n w q Q
  have h : ∀ a b, e.symm (a + b) = e.symm a + e.symm b := by
    intro a b
    let e0 := (susp_invariance (n - 1) (w + q) 1 (-q) Q).trans
      (Iso.homCongr (Iso.refl _) (biSuspensionIso q Q))
    have h0 : e0 (a + b) = e0 a + e0 b := by
      simp [e0, susp_invariance_add, Preadditive.comp_add, Preadditive.add_comp]
    have hc (n' w' : ℤ) (hn : n' = n) (hw : w' = w)
        (e' : BiHom (n - 1) (w + q) Q ≃
          BiHom n' w' (((SyntheticCategory.biShift (0, -q)).obj Q)⟦(1 : ℤ)⟧))
        (he' : e' (a + b) = e' a + e' b)
        (ht : (BiHom (n - 1) (w + q) Q ≃
          BiHom n' w' (((SyntheticCategory.biShift (0, -q)).obj Q)⟦(1 : ℤ)⟧)) =
          (BiHom (n - 1) (w + q) Q ≃
          BiHom n w (((SyntheticCategory.biShift (0, -q)).obj Q)⟦(1 : ℤ)⟧))) :
        (cast ht e') (a + b) = (cast ht e') a + (cast ht e') b := by
      subst n'
      subst w'
      exact he'
    dsimp only [e, biSuspensionHomEquivRaw, Equiv.symm_symm]
    exact hc (n - 1 + 1) (w + q + -q) (sub_add_cancel n 1)
      (add_neg_cancel_right w q) e0 h0 _
  apply e.symm.injective
  rw [h]
  simp [e]

end KIP126.Synthetic.Context
