import KIP126.Def.Synthetic.QuotientTower.Data
import KIP126.Def.Synthetic.Sphere.Data
import KIP126.Def.StableHomotopy.Context.Finiteness.Proofs

namespace KIP126.Synthetic.Context

open CategoryTheory CategoryTheory.Pretriangulated KIP126.StableHomotopy

universe u v
variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  [HasFunctorialCofiber (C := Syn)] {A : Syn}

/-- Finiteness of the relevant weights of the first λ quotient propagates
to every positive finite quotient through the actual λ–ρ–δ triangles. -/
theorem FiniteLambdaQuotientTower.finite_biHom (T : FiniteLambdaQuotientTower A)
    (q : ℕ) (hq : 0 < q) (m w : ℤ)
    (hfinite : ∀ j : ℕ, j < q → Finite (BiHom m (w + j) (XModLambdaN A 1))) :
    Finite (BiHom m w (XModLambdaN A q)) := by
  induction q generalizing w with
  | zero => omega
  | succ q ih =>
    by_cases hq0 : q = 0
    · subst q
      simpa using hfinite 0 (by decide)
    · have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
      haveI : Finite (BiHom m (w + 1) (XModLambdaN A q)) := by
        apply ih hqpos
        intro j hj
        simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using
          hfinite (j + 1) (Nat.succ_lt_succ hj)
      haveI : Finite (BiHom m w
          ((SyntheticCategory.biShift (0, -1)).obj (XModLambdaN A q))) := by
        simpa using Finite.of_equiv (BiHom m (w + 1) (XModLambdaN A q))
          (susp_invariance m (w + 1) 0 (-1) (XModLambdaN A q))
      haveI : Finite (BiHom m w (XModLambdaN A 1)) := by
        simpa using hfinite 0 (by omega)
      let D := T.triangle (i := 1) (j := q + 1) (by decide) (by omega)
      haveI : Finite (Smn m w ⟶ (Triangle.mk D.lambdaMap D.rho D.delta).obj₁) := by
        change Finite (BiHom m w
          ((SyntheticCategory.biShift (0, -1)).obj (XModLambdaN A (q + 1 - 1))))
        simpa only [Nat.add_sub_cancel] using
          (inferInstance : Finite (BiHom m w
            ((SyntheticCategory.biShift (0, -1)).obj (XModLambdaN A q))))
      haveI : Finite (Smn m w ⟶ (Triangle.mk D.lambdaMap D.rho D.delta).obj₃) :=
        (inferInstance : Finite (BiHom m w (XModLambdaN A 1)))
      exact finite_hom_middle_of_distinguished
        (Triangle.mk D.lambdaMap D.rho D.delta) D.distinguished (Smn m w)

end KIP126.Synthetic.Context
