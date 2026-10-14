module

public import KIP126.Def.StableHomotopy.Implementation.HF2.Moore.Postnikov.Cover.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Source.Chosen.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation
open CategoryTheory
set_option backward.isDefEq.respectTransparency false

/-- The actual fiber of the Moore-heart cover of a single-degree exponent-two object. -/
noncomputable def sourceModTwoMooreHeartRelations
    (Y : SourceCategory.{0})
    (hY : ∀ d : ℤ, d ≠ 0 → Subsingleton ((sourceStableHomotopyAddFunctor d).obj Y))
    (h₂ : ∀ y : (sourceStableHomotopyAddFunctor 0).obj Y, 2 • y = 0) : SourceCategory :=
  sourceChosenFiber (sourceModTwoMooreHeartCoverMap Y (fun d hd => hY d (by omega)) h₂)

/-- The original signed fiber boundary includes the relations into the actual cover. -/
noncomputable def sourceModTwoMooreHeartRelationsInclusion
    (Y : SourceCategory.{0})
    (hY : ∀ d : ℤ, d ≠ 0 → Subsingleton ((sourceStableHomotopyAddFunctor d).obj Y))
    (h₂ : ∀ y : (sourceStableHomotopyAddFunctor 0).obj Y, 2 • y = 0) :
    sourceModTwoMooreHeartRelations Y hY h₂ ⟶ sourceModTwoMooreHeartCover Y :=
  sourceChosenFiberInclusion (sourceModTwoMooreHeartCoverMap Y (fun d hd => hY d (by omega)) h₂)

end KIP126.StableHomotopy.Implementation

