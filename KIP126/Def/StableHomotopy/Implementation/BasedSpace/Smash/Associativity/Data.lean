module

public import KIP126.Def.StableHomotopy.Implementation.Generators

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.BasedSpace

open CategoryTheory

universe u

/-- The reverse actual smash associator is built from the already
constructed continuous swaps and forward associator. -/
noncomputable def smashAssocInverse (A B C : BasedSpace.{u}) :
    A.smash (B.smash C) ⟶ (A.smash B).smash C :=
  smashMap (𝟙 A) (smashSwap B C) ≫ smashSwap A (C.smash B) ≫
    smashAssoc C B A ≫ smashMap (𝟙 C) (smashSwap B A) ≫ smashSwap C (A.smash B)

end KIP126.StableHomotopy.Implementation.BasedSpace
