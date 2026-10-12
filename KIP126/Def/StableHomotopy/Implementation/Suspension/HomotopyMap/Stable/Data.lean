module

public import KIP126.Def.StableHomotopy.Implementation.Suspension.HomotopyMap.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum.HomotopyMap

universe u
variable {X Y : Prespectrum.{u}} (f : HomotopyMap X Y)

/-- The map of actual stable homotopy quotients induced by the specified
level maps and bonding homotopies. -/
def stableMap (d : ℤ) : StableHomotopy X d → StableHomotopy Y d :=
  Quot.lift (fun a => Quot.mk _ (f.mapRepresentative a))
    (fun _ _ h => f.mapRepresentative_relation h)

end KIP126.StableHomotopy.Implementation.Prespectrum.HomotopyMap
