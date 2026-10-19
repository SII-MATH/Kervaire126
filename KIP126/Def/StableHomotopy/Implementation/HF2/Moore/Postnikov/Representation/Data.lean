module

public import KIP126.Def.StableHomotopy.Implementation.HF2.Moore.Postnikov.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Representation.Additive.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation
open CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false

/-- Evaluate an actual map from the Moore heart on its original sphere unit,
retaining the original degree-zero stable group and its additive structure. -/
noncomputable def sourceModTwoMooreHeartEvaluation (Y : SourceCategory.{0}) :
    (sourceModTwoMooreHeart ⟶ Y) →+ (sourceStableHomotopyAddFunctor 0).obj Y :=
  (Prespectrum.sourceStableHomotopyAddEquiv Y.as.obj 0).symm.toAddMonoidHom.comp {
    toFun := fun a => sourceModTwoMooreHeartUnit ≫ a
    map_zero' := by simp
    map_add' := fun a b => by rw [Preadditive.comp_add] }

end KIP126.StableHomotopy.Implementation

