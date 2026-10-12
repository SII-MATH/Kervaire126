module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Postnikov
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.CellularCover.Upper.Cofiber.Orthogonality.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Milnor.Colimit.Represented.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory

set_option backward.isDefEq.respectTransparency false

/-- The same constructed truncation unit is universal for maps into every
actual source object with vanishing stable homotopy in degrees at least n.
Its proof uses the actual upper-cell orthogonality and the represented
Milnor difference equation. -/
theorem sourcePostnikovUnit_precomp_bijective
    (X : SourceCategory.{0}) (n : ℤ) (Y : SourceCategory.{0})
    (hY : ∀ d : ℤ, n ≤ d → Subsingleton ((sourceStableHomotopyAddFunctor d).obj Y)) :
    Function.Bijective (fun a : sourcePostnikovTruncation X n ⟶ Y =>
      sourcePostnikovUnit X n ≫ a) := by
  apply sourceHomotopyColimitInclusion_zero_precomp_bijective (sourcePostnikovDiagram X n) Y
  · intro k
    simp only [sourcePostnikovDiagram, Functor.ofSequence_map_homOfLE_succ]
    exact sourceUpperCellKillingUnit_precomp_bijective (sourcePostnikovStage X n k) n Y hY
  · intro k
    simp only [sourcePostnikovDiagram, Functor.ofSequence_map_homOfLE_succ]
    exact (sourceUpperCellKillingUnit_shift_precomp_bijective
      (sourcePostnikovStage X n k) n Y hY).surjective

/-- For an already truncated source object, its actual truncation unit is
an isomorphism, by the proved universal property and actual truncation bounds. -/
theorem sourcePostnikovUnit_isIso_of_truncated (X : SourceCategory.{0}) (n : ℤ)
    (hX : ∀ d : ℤ, n ≤ d → Subsingleton ((sourceStableHomotopyAddFunctor d).obj X)) :
    IsIso (sourcePostnikovUnit X n) := by
  obtain ⟨r, hr⟩ := (sourcePostnikovUnit_precomp_bijective X n X hX).surjective (𝟙 X)
  have hη := (sourcePostnikovUnit_precomp_bijective X n (sourcePostnikovTruncation X n)
    (sourcePostnikovTruncation_homotopy_subsingleton X n)).injective
  have hr' : r ≫ sourcePostnikovUnit X n = 𝟙 _ := by
    apply hη
    dsimp only at hr ⊢
    rw [← Category.assoc, hr, Category.id_comp, Category.comp_id]
  exact ⟨⟨r, hr, hr'⟩⟩

end KIP126.StableHomotopy.Implementation
