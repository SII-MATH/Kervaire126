import KIP126.Def.Synthetic.PageExtension.Lambda.Data

namespace KIP126.Synthetic.Context
open CategoryTheory KIP126.StableHomotopy
universe u v
variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  [HasFunctorialCofiber (C := Syn)] {X : Syn}

set_option backward.isDefEq.respectTransparency false in
/-- The finite scaling map is bound to the existing λ power and quotient
inclusions, rather than to an independently chosen endomorphism. -/
theorem FiniteLambdaQuotientTower.lambdaInclusion_quotient
    (T : FiniteLambdaQuotientTower X) (k q : ℕ) (hkq : k < q) :
    (SyntheticCategory.biShift (0, -(k : ℤ))).map (XModLambdaN.incl X (q - k)) ≫
      T.lambdaInclusion k q hkq = lambdaPow k X ≫ XModLambdaN.incl X q := by
  by_cases hk : k = 0
  · subst k
    change (SyntheticCategory.biShift (0, 0)).map (XModLambdaN.incl X q) ≫
      SyntheticCategory.biShift_zero.hom.app (XModLambdaN X q) =
      SyntheticCategory.biShift_zero.hom.app X ≫ XModLambdaN.incl X q
    exact SyntheticCategory.biShift_zero.hom.naturality (XModLambdaN.incl X q)
  · simpa only [lambdaInclusion, dif_neg hk] using
      (T.triangle (Nat.pos_of_ne_zero hk) hkq).lambda_quotient

end KIP126.Synthetic.Context
