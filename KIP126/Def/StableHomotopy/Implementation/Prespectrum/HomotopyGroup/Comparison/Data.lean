module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Colimit.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

universe u

/-- Send the original stable quotient to the cofinal direct limit using
only the actual stabilization of its representatives. -/
noncomputable def stableGroupCode (X : Prespectrum.{u}) (d : ℤ) :
    StableHomotopy X d → stableGroupColimit X d :=
  Quot.lift Representative.groupColimit (fun a _ h => by
    cases h with
    | homotopy p h => exact a.groupColimit_homotopy p h
    | stabilization => exact a.groupColimit_next)

/-- Realize a direct-limit element as its original stable cubical class. -/
noncomputable def stableGroupRealize (X : Prespectrum.{u}) (d : ℤ) :
    stableGroupColimit X d → StableHomotopy X d :=
  DirectLimit.lift (stableLevelTransition X d) (stableLevelClass X d)
    (stableLevelClass_transition X d)

end KIP126.StableHomotopy.Implementation.Prespectrum
