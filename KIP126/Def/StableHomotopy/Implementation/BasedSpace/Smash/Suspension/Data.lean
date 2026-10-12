module

public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.Smash.Suspension.Existence.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.BasedSpace
open CategoryTheory Topology

/-- Actual interchange map with an arbitrary second smash factor. -/
noncomputable def smashSuspensionComparison (A B : BasedSpace.{0})
    [UCompactlyGeneratedSpace.{0} A] : A.suspension.smash B ⟶ (A.smash B).suspension :=
  (smashSuspensionComparison_exists A B).exists.choose

/-- Actual reverse interchange map. -/
noncomputable def smashSuspensionInverse (A B : BasedSpace.{0}) :
    (A.smash B).suspension ⟶ A.suspension.smash B :=
  (smashSuspensionInverse_exists A B).exists.choose

end KIP126.StableHomotopy.Implementation.BasedSpace
