module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Unit.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
set_option backward.isDefEq.respectTransparency false

/-- For original compactly generated levels, the actual zero-sphere
unit section is continuous and forms a strict prespectrum map. -/
def spaceSmashUnitInverse (X : Prespectrum.{0})
    [∀ n, UCompactlyGeneratedSpace.{0} (X.level n)] :
    X ⟶ spaceSmash BasedSpace.zeroSphere X where
  level n := ⟨fun x => BasedSpace.smashPoint BasedSpace.zeroSphere (X.level n)
      (show BasedSpace.zeroSphere from (1 : Fin 2)) x, by
    apply continuous_from_uCompactlyGeneratedSpace
    intro S g
    exact BasedSpace.continuous_smashPoint_compact BasedSpace.zeroSphere (X.level n)
      (ContinuousMap.const S (show BasedSpace.zeroSphere from (1 : Fin 2))) g⟩
  point n := BasedSpace.smashPoint_base_right _ _ _
  bond n x t := (spaceSmash_bond BasedSpace.zeroSphere X n _ x t).symm

end KIP126.StableHomotopy.Implementation.Prespectrum
