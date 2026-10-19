module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Unit.Inverse.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory

@[simp] theorem spaceSmashUnit_inverse (X : Prespectrum.{0})
    [∀ n, UCompactlyGeneratedSpace.{0} (X.level n)] :
    spaceSmashUnit X ≫ spaceSmashUnitInverse X = 𝟙 _ := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  exact BasedSpace.smashUnitComparison_section (X.level n)

@[simp] theorem spaceSmashUnitInverse_unit (X : Prespectrum.{0})
    [∀ n, UCompactlyGeneratedSpace.{0} (X.level n)] :
    spaceSmashUnitInverse X ≫ spaceSmashUnit X = 𝟙 X := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  exact BasedSpace.smashUnitComparison_apply (X.level n)

end KIP126.StableHomotopy.Implementation.Prespectrum
