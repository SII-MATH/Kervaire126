import KIPBase.Section7.BjmBxCriterion

namespace KIPBase.Section7

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.MonoidalCategory
  KIPBase.StableHomotopy KIPBase.Synthetic

universe u v

/-- The direct Table 1 consequence used at the end of Proposition 7.9. -/
theorem table1_contradiction
    (Syn : Type u) [Category.{v} Syn] [Preadditive Syn]
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [MonoidalCategory Syn] [Pretriangulated Syn] [SyntheticCategory Syn]
    (h3 : Statement7_8_3) (h5prime : Statement7_11_5prime (Syn := Syn)) :
    False :=
  table1 (Syn := Syn) h3 h5prime

end KIPBase.Section7
