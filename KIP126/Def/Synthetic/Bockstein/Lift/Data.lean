import KIP126.Def.Synthetic.QuotientTower.Proofs
import KIP126.Def.Synthetic.Bockstein.Maps.Data

/-!
# Direct finite-quotient Bockstein lift data

These definitions package the proved finite-tower part of the historical
Adams--Bockstein work.  They use the supplied KIP126 quotient tower and keep
the chosen lift explicit; no comparison with a classical Adams page is
assumed here.
-/

namespace KIP126.Synthetic.Bockstein.Lift

open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy KIP126.Synthetic.Context

universe u v

variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  [HasFunctorialCofiber (C := Syn)] {X : Syn}

/-- The group of classes represented in the first finite quotient. -/
abbrev V (X T : Syn) : Type _ := T ⟶ XModLambdaN X 1

/-- Restriction of a class represented at exponent `i + 1` to the first
quotient. -/
noncomputable def lift
    (Q : FiniteLambdaQuotientTower X) (T : Syn) (i : ℕ) :
    (T ⟶ XModLambdaN X (i + 1)) →+ V X T where
  toFun a := a ≫ Q.rho 1 (i + 1) (Nat.succ_le_succ (Nat.zero_le i))
  map_zero' := zero_comp
  map_add' _ _ := by simp only [Preadditive.add_comp]

/-- Classes in the first quotient which admit a lift through exponent `i+1`. -/
noncomputable def cycles
    (Q : FiniteLambdaQuotientTower X) (T : Syn) (i : ℕ) :
    AddSubgroup (V X T) := (lift Q T i).range

/-- The raw connecting map associated with a chosen finite lift. -/
noncomputable def obstruction
    (X T : Syn) (i : ℕ) :
    (T ⟶ XModLambdaN X (i + 1)) →+
      (T ⟶ (shiftFunctor Syn (1 : ℤ)).obj
        ((SyntheticCategory.biShift (0, -((i + 1 : ℕ) : ℤ))).obj
          (XModLambdaN X 1))) where
  toFun a := a ≫ XModLambdaN.proj X (i + 1) ≫
    (shiftFunctor Syn (1 : ℤ)).map
      ((SyntheticCategory.biShift (0, -((i + 1 : ℕ) : ℤ))).map
        (XModLambdaN.incl X 1))
  map_zero' := by simp only [zero_comp]
  map_add' _ _ := by simp only [Preadditive.add_comp]

end KIP126.Synthetic.Bockstein.Lift
