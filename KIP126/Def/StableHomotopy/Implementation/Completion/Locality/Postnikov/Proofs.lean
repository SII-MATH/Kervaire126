module

public import KIP126.Def.StableHomotopy.Implementation.Completion.Locality.Milnor.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Postnikov.Layer.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Postnikov.Orthogonality.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Postnikov.Limit.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
set_option backward.isDefEq.respectTransparency false

private theorem local_of_zero (X : SourceCategory.{0}) (hX : IsZero X) : SourceIsHF2Local X := by
  intro A B f _
  exact ⟨fun a b _ => hX.eq_of_tgt a b, fun a => ⟨hX.from_ B,hX.eq_of_tgt _ a⟩⟩

/-- The actual finite Postnikov sections of a bounded-below spectrum are
local whenever its actual layers above the bound are local. -/
theorem sourcePostnikovTruncation_isHF2Local_of_layers (X : SourceCategory.{0}) (N : ℤ)
    (hX : ∀ d, d < N → Subsingleton ((sourceStableHomotopyAddFunctor d).obj X))
    (hL : ∀ d, N ≤ d → SourceIsHF2Local (sourcePostnikovLayer X d)) (n : ℤ) :
    SourceIsHF2Local (sourcePostnikovTruncation X n) := by
  have hsteps : ∀ j : ℕ, SourceIsHF2Local (sourcePostnikovTruncation X (N+j)) := by
    intro j
    induction j with
    | zero =>
      simp only [Nat.cast_zero, add_zero]
      exact local_of_zero _ (sourcePostnikovTruncation_isZero_of_connective X N hX)
    | succ j ih =>
      let f := sourcePostnikovRestriction X (N+j+1) (N+j) (by omega)
      let T := sourceChosenFiberTriangle f
      have hT := sourceChosenFiberTriangle_distinguished f
      have h₁ : SourceIsHF2Local T.obj₁ := hL (N+j) (by omega)
      have h₂ : SourceIsHF2Local T.obj₂ :=
        SourceIsHF2Local.triangle_first T.rotate (rot_of_distTriang T hT) ih h₁.suspension
      change SourceIsHF2Local (sourcePostnikovTruncation X (N+j+1)) at h₂
      rw [Nat.cast_succ, ← add_assoc]
      exact @h₂
  intro A B f hf
  by_cases hn : N ≤ n
  · have hj : N + ((n-N).toNat : ℤ) = n := by
      rw [Int.toNat_of_nonneg (sub_nonneg.mpr hn)]
      omega
    have h : SourceIsHF2Local (sourcePostnikovTruncation X (N+((n-N).toNat : ℤ))) :=
      @hsteps (n-N).toNat
    rw [hj] at h
    exact h f hf
  · exact local_of_zero _ (sourcePostnikovTruncation_isZero_of_connective X n
      (fun d hd => hX d (by omega))) f hf

/-- Actual Postnikov convergence reduces HF2 locality of a bounded-below
source object to locality of its actual single-degree layers. -/
theorem sourceIsHF2Local_of_boundedBelow_layers (X : SourceCategory.{0}) (N : ℤ)
    (hX : ∀ d, d < N → Subsingleton ((sourceStableHomotopyAddFunctor d).obj X))
    (hL : ∀ d, N ≤ d → SourceIsHF2Local (sourcePostnikovLayer X d)) : SourceIsHF2Local X :=
  SourceIsHF2Local.of_iso (asIso (sourcePostnikovLimitUnit X))
    (SourceIsHF2Local.sourceHomotopyLimit (sourcePostnikovTower X)
      (fun n => sourcePostnikovTruncation_isHF2Local_of_layers X N hX hL n))

end KIP126.StableHomotopy.Implementation
