module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Postnikov.Universal.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Zero.Detection.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false

/-- Truncating an actual source object below its lower connectivity bound
gives a genuine zero object, detected by the original stable groups. -/
theorem sourcePostnikovTruncation_isZero_of_connective (X : SourceCategory.{0}) (n : ℤ)
    (hX : ∀ d, d < n → Subsingleton ((sourceStableHomotopyAddFunctor d).obj X)) :
    IsZero (sourcePostnikovTruncation X n) := by
  apply Prespectrum.source_isZero_of_stableHomotopy_subsingleton
  intro d
  by_cases hd : d < n
  · letI := hX d hd
    exact (sourcePostnikovUnit_homotopy_bijective X n d hd).surjective.subsingleton
  · exact sourcePostnikovTruncation_homotopy_subsingleton X n d (by omega)

/-- Actual source spectra with disjoint lower and upper stable-degree
bounds are orthogonal. This is proved from the constructed truncation
and its actual universal unit. -/
theorem source_hom_subsingleton_of_degree_bounds (X Y : SourceCategory.{0}) (n : ℤ)
    (hX : ∀ d, d < n → Subsingleton ((sourceStableHomotopyAddFunctor d).obj X))
    (hY : ∀ d, n ≤ d → Subsingleton ((sourceStableHomotopyAddFunctor d).obj Y)) :
    Subsingleton (X ⟶ Y) := by
  have hτ := sourcePostnikovTruncation_isZero_of_connective X n hX
  letI : Subsingleton (sourcePostnikovTruncation X n ⟶ Y) := ⟨fun a b => hτ.eq_of_src a b⟩
  exact (sourcePostnikovUnit_precomp_bijective X n Y hY).surjective.subsingleton

end KIP126.StableHomotopy.Implementation
