module

public import KIP126.Def.StableHomotopy.Implementation.HF2.Moore.Postnikov.Representation.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation
open CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false

/-- Actual Moore-heart maps represent the original stable group of any
upper-truncated exponent-two target, additively. -/
noncomputable def sourceModTwoMooreHeartHomEquiv
    (Y : SourceCategory.{0})
    (hY : ∀ d : ℤ, 1 ≤ d → Subsingleton ((sourceStableHomotopyAddFunctor d).obj Y))
    (h₂ : ∀ y : (sourceStableHomotopyAddFunctor 0).obj Y, 2 • y = 0) :
    (sourceModTwoMooreHeart ⟶ Y) ≃+ (sourceStableHomotopyAddFunctor 0).obj Y :=
  AddEquiv.ofBijective (sourceModTwoMooreHeartEvaluation Y)
    (sourceModTwoMooreHeartEvaluation_bijective Y hY h₂)

/-- The actual coproduct of Moore hearts indexed by the original stable
classes of the target. -/
noncomputable def sourceModTwoMooreHeartCover (Y : SourceCategory.{0}) : SourceCategory.{0} :=
  ∐ fun _ : (sourceStableHomotopyAddFunctor 0).obj Y => sourceModTwoMooreHeart

/-- Send each actual Moore-heart summand to its specified original class. -/
noncomputable def sourceModTwoMooreHeartCoverMap
    (Y : SourceCategory.{0})
    (hY : ∀ d : ℤ, 1 ≤ d → Subsingleton ((sourceStableHomotopyAddFunctor d).obj Y))
    (h₂ : ∀ y : (sourceStableHomotopyAddFunctor 0).obj Y, 2 • y = 0) :
    sourceModTwoMooreHeartCover Y ⟶ Y :=
  Sigma.desc (fun y => (sourceModTwoMooreHeartHomEquiv Y hY h₂).symm y)

end KIP126.StableHomotopy.Implementation

