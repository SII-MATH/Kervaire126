module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Postnikov.Tower.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Milnor.Data
public import KIP126.Def.StableHomotopy.InverseSequence.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory

/-- The original compatible truncation units lift to the actual Milnor
homotopy limit of the constructed Postnikov tower. -/
noncomputable def sourcePostnikovLimitUnit (X : SourceCategory.{0}) :
    X ⟶ sourceHomotopyLimit (sourcePostnikovTower X) :=
  ((sourceHomotopyLimitWitness (sourcePostnikovTower X)).exists_lift
    (fun k => sourcePostnikovUnit X k) (sourcePostnikovTower_unit_step X)).choose

end KIP126.StableHomotopy.Implementation
