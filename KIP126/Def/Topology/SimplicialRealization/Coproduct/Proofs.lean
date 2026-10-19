module

public import KIP126.Def.Topology.SimplicialRealization.Coproduct.Data
public import KIP126.Def.Topology.SimplicialRealization.Relative.Proofs
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory CategoryTheory.Limits

universe u

set_option backward.isDefEq.respectTransparency false

/-- The displayed first inclusion has its exact prescribed composite. -/
theorem simplicialSumInl_desc {K L T : SSet.{u}} (f : K ⟶ T) (g : L ⟶ T) :
    simplicialSumInl K L ≫ simplicialSumDesc f g = f := rfl

/-- The displayed second inclusion has its exact prescribed composite. -/
theorem simplicialSumInr_desc {K L T : SSet.{u}} (f : K ⟶ T) (g : L ⟶ T) :
    simplicialSumInr K L ≫ simplicialSumDesc f g = g := rfl

/-- Disjoint degreewise injections give an actual monomorphism from
the displayed simplicial coproduct. -/
theorem simplicialSumDesc_mono {K L T : SSet.{u}} (f : K ⟶ T) (g : L ⟶ T)
    (hf : ∀ a, Function.Injective (f.app a))
    (hg : ∀ a, Function.Injective (g.app a))
    (hd : ∀ a x y, f.app a x ≠ g.app a y) : Mono (simplicialSumDesc f g) := by
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro a
  apply (CategoryTheory.mono_iff_injective _).mpr
  rintro (x | x) (y | y) h
  · exact congrArg Sum.inl (hf a h)
  · exact (hd a x y h).elim
  · exact (hd a y x h.symm).elim
  · exact congrArg Sum.inr (hg a h)

end KIP126.Topology.SimplicialRealization
