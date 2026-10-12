module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Postnikov.Restriction.Proofs
public import KIP126.Def.StableHomotopy.InverseSequence.Data

@[expose] public section

section

namespace KIP126.StableHomotopy.Implementation

/-- The actual Postnikov tower, using cutoffs 0, 1, 2, ... and the original
universal-property restrictions between the constructed truncation objects. -/
noncomputable def sourcePostnikovTower (X : SourceCategory.{0}) : InverseSequence SourceCategory.{0} where
  obj k := sourcePostnikovTruncation X (k : ℤ)
  step k := sourcePostnikovRestriction X (k+1 : ℕ) k (by omega)

end KIP126.StableHomotopy.Implementation

end

section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory

set_option backward.isDefEq.respectTransparency false

/-- Every cutoff restriction is surjective on every original stable group.
Below the lower cutoff both units identify the group, and above it the
target group is zero. -/
theorem sourcePostnikovRestriction_homotopy_surjective
    (X : SourceCategory.{0}) (m n d : ℤ) (h : n ≤ m) :
    Function.Surjective ((sourceStableHomotopyAddFunctor d).map
      (sourcePostnikovRestriction X m n h)) := by
  let G := sourceStableHomotopyAddFunctor d
  by_cases hd : d < n
  · intro y
    obtain ⟨x, hx⟩ := (sourcePostnikovUnit_homotopy_bijective X n d hd).surjective y
    refine ⟨G.map (sourcePostnikovUnit X m) x, ?_⟩
    change (G.map (sourcePostnikovUnit X m) ≫ G.map (sourcePostnikovRestriction X m n h)) x = y
    rw [← G.map_comp, sourcePostnikovUnit_restriction]
    exact hx
  · letI := sourcePostnikovTruncation_homotopy_subsingleton X n d (le_of_not_gt hd)
    intro y
    exact ⟨0, Subsingleton.elim _ _⟩

/-- The original units form a compatible family into the actual Postnikov tower. -/
@[reassoc (attr := simp)]
theorem sourcePostnikovTower_unit_step (X : SourceCategory.{0}) (k : ℕ) :
    sourcePostnikovUnit X (k+1 : ℕ) ≫ (sourcePostnikovTower X).step k =
      sourcePostnikovUnit X k :=
  sourcePostnikovUnit_restriction X (k+1 : ℕ) k (by omega)

/-- Every transition of this actual tower is surjective in every stable degree. -/
theorem sourcePostnikovTower_homotopy_surjective (X : SourceCategory.{0}) (d : ℤ) (k : ℕ) :
    Function.Surjective ((sourceStableHomotopyAddFunctor d).map
      ((sourcePostnikovTower X).step k)) :=
  sourcePostnikovRestriction_homotopy_surjective X (k+1 : ℕ) k d (by omega)

end KIP126.StableHomotopy.Implementation

end
