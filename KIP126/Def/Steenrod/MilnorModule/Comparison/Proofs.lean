import KIP126.Def.Steenrod.MilnorModule.Comparison.Predicates

/-!
Existence of the prescribed Ext comparison remains a proof obligation.
The all-cocycle representative condition determines it uniquely; no chosen
comparison is introduced as data or as an additional stage assumption.
-/

namespace KIP126.Steenrod.Milnor.Module

open CategoryTheory KIP126.Core.Algebra

/-- Same-degree dualization of the fixed cofree resolution induces the
left-module Ext comparison, with its exact representative formula. -/
theorem exists_dualCobarComparison (R : Ext.CobarResolution) :
    ∃ e : ∀ (s : ℕ) (t : ℤ), Ext.SphereExt s t ≃ₗ[F2] SphereExt s t,
      PreservesDualCobarRepresentatives R e := by
  sorry

/-- Agreement on all actual resolution cocycles leaves no freedom to choose
an unrelated linear equivalence. This also covers cohomological degree zero. -/
theorem dualCobarComparison_unique (R : Ext.CobarResolution)
    {e e' : ∀ (s : ℕ) (t : ℤ), Ext.SphereExt s t ≃ₗ[F2] SphereExt s t}
    (he : PreservesDualCobarRepresentatives R e)
    (he' : PreservesDualCobarRepresentatives R e') : e = e' := by
  funext s t
  apply LinearEquiv.ext
  intro x
  obtain ⟨f, hf, rfl⟩ := R.resolution.extMk_surjective x (s + 1) rfl
  obtain ⟨_, h⟩ := he s t f hf
  obtain ⟨_, h'⟩ := he' s t f hf
  exact h.trans h'.symm

end KIP126.Steenrod.Milnor.Module
