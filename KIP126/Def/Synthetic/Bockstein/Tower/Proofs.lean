import KIP126.Def.Synthetic.Bockstein.Tower.Data

/-! Basic checks on the actual residual tower and its first-page convention. -/

namespace KIP126.Synthetic.Bockstein

open CategoryTheory
open KIP126.StableHomotopy KIP126.Synthetic.Context

universe u v

variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]

/-- The negative tail retains the same specified zero-shift object. -/
theorem lambdaTower_obj_nonpos (A : Syn) (k : ℤ) (hk : k ≤ 0) :
    (lambdaTower A).obj k = (SyntheticCategory.biShift (0, 0)).obj A := by
  change (SyntheticCategory.biShift (0, -(k.toNat : ℤ))).obj A = _
  have hk' : k.toNat = 0 := by omega
  simp only [hk', Nat.cast_zero, neg_zero]

/-- At nonnegative integer stages this is precisely the original residual
sequence, including its actual zeroth object. -/
theorem lambdaTower_obj_nat (A : Syn) (k : ℕ) :
    (lambdaTower A).obj (k : ℤ) =
      (SyntheticCategory.biShift (0, -(k : ℤ))).obj A := by
  simp only [lambdaTower, InverseSequence.toDescendingTower,
    lambdaResidualSequence, Int.toNat_natCast]

variable [HasFunctorialCofiber (C := Syn)]

@[simp] theorem weightwiseSequence_firstPage (A : Syn) (w : ℤ) :
    (weightwiseSequence A w).r₀ = 1 := rfl

@[simp] theorem weightwiseSequence_diffDeg (A : Syn) (w q : ℤ) :
    (weightwiseSequence A w).diffDeg q = (q, -1) := rfl

end KIP126.Synthetic.Bockstein
