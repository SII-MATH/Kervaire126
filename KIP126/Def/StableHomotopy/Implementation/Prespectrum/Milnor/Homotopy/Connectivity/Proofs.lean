module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Milnor.Homotopy.Equivalence.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

/-- Actual degreewise vanishing passes to the constructed Milnor limit
when the next-degree stable groups are finite. -/
theorem sourceHomotopyLimit_homotopy_subsingleton_of_finite
    (D : InverseSequence SourceCategory.{0}) (d : ℤ)
    [∀ k, Subsingleton ((sourceStableHomotopyAddFunctor d).obj (D.obj k))]
    [∀ k, Finite ((sourceStableHomotopyAddFunctor (d+1)).obj (D.obj k))] :
    Subsingleton ((sourceStableHomotopyAddFunctor d).obj (sourceHomotopyLimit D)) :=
  (sourceHomotopyLimitComparison_injective_of_finite D d).subsingleton

/-- A uniform lower homotopy bound is retained by the actual source
Milnor limit when the groups at the bound are finite. -/
theorem sourceHomotopyLimit_boundedBelow_of_finite
    (D : InverseSequence SourceCategory.{0}) (N : ℤ)
    (hD : ∀ k d, d < N → Subsingleton ((sourceStableHomotopyAddFunctor d).obj (D.obj k)))
    (hN : ∀ k, Finite ((sourceStableHomotopyAddFunctor N).obj (D.obj k))) :
    ∀ d, d < N → Subsingleton ((sourceStableHomotopyAddFunctor d).obj (sourceHomotopyLimit D)) := by
  intro d hd
  letI (k : ℕ) := hD k d hd
  letI (k : ℕ) : Finite ((sourceStableHomotopyAddFunctor (d+1)).obj (D.obj k)) := by
    by_cases h : d+1 < N
    · letI := hD k (d+1) h
      infer_instance
    · have he : d+1 = N := by omega
      rw [he]
      exact hN k
  exact sourceHomotopyLimit_homotopy_subsingleton_of_finite D d

end KIP126.StableHomotopy.Implementation
