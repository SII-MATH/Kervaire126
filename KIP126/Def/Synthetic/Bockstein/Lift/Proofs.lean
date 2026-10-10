import KIP126.Def.Synthetic.Bockstein.Lift.Data

/-! Elementary finite-lift filtration laws. -/

namespace KIP126.Synthetic.Bockstein.Lift

open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context

universe u v

variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  [HasFunctorialCofiber (C := Syn)] {X : Syn}

theorem mem_cycles_iff
    (Q : FiniteLambdaQuotientTower X) (T : Syn) (i : ℕ)
    (x : V X T) :
    x ∈ cycles Q T i ↔
      ∃ a : T ⟶ XModLambdaN X (i + 1), lift Q T i a = x :=
  Iff.rfl

theorem lift_restrict
    (Q : FiniteLambdaQuotientTower X) (T : Syn)
    {i j : ℕ} (hij : i ≤ j) (a : T ⟶ XModLambdaN X (j + 1)) :
    lift Q T i
        (a ≫ Q.rho (i + 1) (j + 1) (Nat.succ_le_succ hij)) =
      lift Q T j a := by
  change (a ≫ Q.rho (i + 1) (j + 1) (Nat.succ_le_succ hij)) ≫
      Q.rho 1 (i + 1) (Nat.succ_le_succ (Nat.zero_le i)) =
    a ≫ Q.rho 1 (j + 1) (Nat.succ_le_succ (Nat.zero_le j))
  rw [Category.assoc, Q.rho_trans
    (Nat.succ_le_succ (Nat.zero_le i)) (Nat.succ_le_succ hij)]

theorem cycles_anti
    (Q : FiniteLambdaQuotientTower X) (T : Syn)
    {i j : ℕ} (hij : i ≤ j) :
    cycles Q T j ≤ cycles Q T i := by
  rintro x ⟨a, rfl⟩
  refine ⟨a ≫ Q.rho (i + 1) (j + 1) (Nat.succ_le_succ hij), ?_⟩
  exact lift_restrict Q T hij a

end KIP126.Synthetic.Bockstein.Lift
