/-
  KIPBase.Synthetic.QuotientExtensionSS
  Extension spectral sequences attached to finite quotient restrictions.
-/
import KIPBase.Synthetic.ExtensionSS
import KIPBase.Synthetic.QuotientTower

namespace KIPBase.Synthetic

open CategoryTheory CategoryTheory.Limits KIPBase.SpectralSequence

universe u v

variable {Syn : Type u} [Category.{v} Syn] [Preadditive Syn]
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [MonoidalCategory Syn]
    [Pretriangulated Syn] [SyntheticCategory Syn]

/-- Convergence-and-detection data for the extension spectral sequence of a
finite quotient restriction `ρ_{i,j} : X/λ^j ⟶ X/λ^i`. -/
abbrev RhoExtensionData {X : Syn} (T : FiniteLambdaQuotientTower X)
    (i j : ℕ) (hij : i ≤ j) :=
  SyntheticExtensionData (T.rho i j hij)

/-- The elementary `ρ_{i,j}`-extension spectral sequence at a fixed
synthetic stem and weight. -/
noncomputable def rhoESS {X : Syn} (T : FiniteLambdaQuotientTower X)
    (i j : ℕ) (hij : i ≤ j) (data : RhoExtensionData T i j hij)
    (degree : ℤ × ℤ) :
    SpectralSequence (AddCommGrpCat.{0}) (ℤ × ℤ) :=
  data.ess degree

/-- The `d₀` component in the elementary `ρ_{i,j}`-ESS. -/
noncomputable def rhoESSd0 {X : Syn} (T : FiniteLambdaQuotientTower X)
    (i j : ℕ) (hij : i ≤ j) (data : RhoExtensionData T i j hij)
    (s : ℤ) (degree : ℤ × ℤ) :
    data.e0Source s degree ⟶ data.e0Target s degree :=
  data.d0 s degree

/-- A `ρ`-ESS differential has tridegree `(r,r,0)` and therefore preserves
synthetic weight. -/
theorem rhoESS_tridegree {X : Syn} (T : FiniteLambdaQuotientTower X)
    (i j : ℕ) (hij : i ≤ j) (data : RhoExtensionData T i j hij)
    (s r : ℤ) (degree : ℤ × ℤ) :
    syntheticAdamsIndex (s + r) degree =
      syntheticAdamsIndex s degree + syntheticESSDiffDegree r :=
  data.ess_tridegree s r degree

end KIPBase.Synthetic
