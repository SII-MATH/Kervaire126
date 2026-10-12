module

public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.Smash.Unit.Existence.Proofs

@[expose] public section
namespace KIP126.StableHomotopy.Implementation.BasedSpace
open CategoryTheory
noncomputable def smashUnitComparison (A : BasedSpace.{0}) : zeroSphere.smash A ⟶ A :=
  (smashUnitComparison_exists A).exists.choose
end KIP126.StableHomotopy.Implementation.BasedSpace
