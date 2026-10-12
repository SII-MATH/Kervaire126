module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Moore.Cofiber.Data
public import KIP126.Def.StableHomotopy.Completion.Moore.Proofs
public import KIP126.Def.StableHomotopy.InverseSequence.HomotopyLimit.Represented.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory

universe u

/-- The actual Moore completion candidate in the original source category,
formed from the existing scalar-power tower using its constructed cofibers
and constructed Milnor homotopy limit. -/
noncomputable def sourceMooreCompletion (p : ℕ) (X : SourceCategory.{u}) : SourceCategory.{u} :=
  sourceHomotopyLimit (moorePowerSequence p X)

/-- The actual compatible cofiber inclusions lift through the constructed
Milnor triangle to a chosen Moore unit. -/
noncomputable def sourceMooreCompletionUnit (p : ℕ) (X : SourceCategory.{u}) :
    X ⟶ sourceMooreCompletion p X :=
  ((sourceHomotopyLimitWitness (moorePowerSequence p X)).exists_lift
    (fun k => HasFunctorialCofiber.cofibι (moorePowerMap p X k))
    (moorePowerSequence_inclusion_step p X)).choose

end KIP126.StableHomotopy.Implementation
