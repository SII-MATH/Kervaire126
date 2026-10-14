module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Moore.Triangle.Predicates
public import Mathlib.CategoryTheory.HomCongr

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory

universe u

set_option backward.isDefEq.respectTransparency false

/-- The actual Moore object satisfies the named scalar orthogonality
condition by the already proved tower argument. -/
theorem sourceMooreCompletion_scalarComplete (p : ℕ) (X : SourceCategory.{u}) :
    SourceIsScalarComplete p (sourceMooreCompletion p X) := by
  intro U hU
  letI := hU
  exact sourceMooreCompletion_hom_subsingleton p X U

theorem SourceIsScalarComplete.of_iso {p : ℕ} {X Y : SourceCategory.{u}}
    (e : X ≅ Y) (hY : SourceIsScalarComplete p Y) : SourceIsScalarComplete p X := by
  intro U hU
  letI := hY U hU
  exact (Iso.homCongr (Iso.refl U) e).injective.subsingleton

/-- Every actual coherent integer shift preserves scalar orthogonality. -/
theorem SourceIsScalarComplete.shift {p : ℕ} {X : SourceCategory.{u}}
    (hX : SourceIsScalarComplete p X) (d : ℤ) : SourceIsScalarComplete p (X⟦d⟧) := by
  intro U hU
  letI := hU
  letI := hX (U⟦-d⟧) (isIso_nsmul_id_shift p U (-d))
  let e : (U⟦-d⟧ ⟶ X) ≃ (U ⟶ X⟦d⟧) :=
    (shiftEquiv' SourceCategory (-d) d (neg_add_cancel d)).toAdjunction.homEquiv U X
  exact e.symm.injective.subsingleton

/-- The shifted original Moore unit has the same universal extension
property into every scalar-complete target. -/
theorem sourceMooreCompletionUnit_shift_precomp_bijective
    (p : ℕ) (X L : SourceCategory.{u}) (d : ℤ) (hL : SourceIsScalarComplete p L) :
    Function.Bijective (fun a : (sourceMooreCompletion p X)⟦d⟧ ⟶ L =>
      (sourceMooreCompletionUnit p X)⟦d⟧' ≫ a) := by
  let adj := (shiftEquiv SourceCategory d).toAdjunction
  have h := sourceMooreCompletionUnit_precomp_bijective p X (L⟦-d⟧) (hL.shift (-d))
  constructor
  · intro a b hab
    apply (adj.homEquiv _ _).injective
    apply h.injective
    exact (adj.homEquiv_naturality_left (sourceMooreCompletionUnit p X) a).symm.trans
      ((congrArg (adj.homEquiv X L) hab).trans
        (adj.homEquiv_naturality_left (sourceMooreCompletionUnit p X) b))
  · intro a
    obtain ⟨b,hb⟩ := h.surjective ((adj.homEquiv X L) a)
    refine ⟨(adj.homEquiv (sourceMooreCompletion p X) L).symm b, ?_⟩
    apply (adj.homEquiv X L).injective
    exact (adj.homEquiv_naturality_left (sourceMooreCompletionUnit p X)
      ((adj.homEquiv (sourceMooreCompletion p X) L).symm b)).trans
        ((congrArg (fun q => sourceMooreCompletionUnit p X ≫ q)
          ((adj.homEquiv (sourceMooreCompletion p X) L).apply_symm_apply b)).trans hb)

end KIP126.StableHomotopy.Implementation
