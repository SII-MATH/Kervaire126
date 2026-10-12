module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Postnikov.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.CellularCover.Upper.Cofiber.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Milnor.Colimit.Homotopy.Inclusion.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory

set_option backward.isDefEq.respectTransparency false

/-- Every actual stage map annihilates each degree at or above the cutoff. -/
theorem sourcePostnikovStageMap_homotopy_eq_zero
    (X : SourceCategory.{0}) (n d : ℤ) (hd : n ≤ d) (k : ℕ) :
    (sourceStableHomotopyAddFunctor d).map
      ((sourcePostnikovDiagram X n).map (homOfLE (Nat.le_succ k))) = 0 := by
  simp only [sourcePostnikovDiagram, Functor.ofSequence_map_homOfLE_succ]
  change (sourceStableHomotopyAddFunctor d).map
    (sourceUpperCellKillingUnit (sourcePostnikovStage X n k) n) = 0
  exact sourceUpperCellKillingUnit_map_eq_zero _ n d hd

/-- Every actual stage map preserves all degrees below the cutoff. -/
theorem sourcePostnikovStageMap_homotopy_bijective
    (X : SourceCategory.{0}) (n d : ℤ) (hd : d < n) (k : ℕ) :
    Function.Bijective ((sourceStableHomotopyAddFunctor d).map
      ((sourcePostnikovDiagram X n).map (homOfLE (Nat.le_succ k)))) := by
  simp only [sourcePostnikovDiagram, Functor.ofSequence_map_homOfLE_succ]
  change Function.Bijective ((sourceStableHomotopyAddFunctor d).map
    (sourceUpperCellKillingUnit (sourcePostnikovStage X n k) n))
  exact sourceUpperCellKillingUnit_bijective _ n d hd

/-- The constructed truncation has zero stable homotopy in every degree
at or above n. Each represented class is killed in the immediately following
actual stage. -/
theorem sourcePostnikovTruncation_homotopy_subsingleton
    (X : SourceCategory.{0}) (n d : ℤ) (hd : n ≤ d) :
    Subsingleton ((sourceStableHomotopyAddFunctor d).obj (sourcePostnikovTruncation X n)) := by
  let F := sourcePostnikovDiagram X n
  have hz (x : (sourceStableHomotopyAddFunctor d).obj (sourcePostnikovTruncation X n)) :
      x = 0 := by
    obtain ⟨k, y, rfl⟩ := sourceHomotopyColimit_stableHomotopy_exists_rep F d x
    apply (sourceHomotopyColimit_stableHomotopy_eq_zero_iff F d k y).mpr
    refine ⟨k+1, Nat.le_succ k, ?_⟩
    change (sourceStableHomotopyAddFunctor d).map
      ((sourcePostnikovDiagram X n).map (homOfLE (Nat.le_succ k))) y = 0
    rw [sourcePostnikovStageMap_homotopy_eq_zero X n d hd k]
    rfl
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

/-- The actual truncation unit preserves the original stable homotopy
groups in every degree below n. -/
theorem sourcePostnikovUnit_homotopy_bijective
    (X : SourceCategory.{0}) (n d : ℤ) (hd : d < n) :
    Function.Bijective ((sourceStableHomotopyAddFunctor d).map (sourcePostnikovUnit X n)) :=
  sourceHomotopyColimitInclusion_stableHomotopy_bijective (sourcePostnikovDiagram X n) d
    (sourcePostnikovStageMap_homotopy_bijective X n d hd) 0

end KIP126.StableHomotopy.Implementation
