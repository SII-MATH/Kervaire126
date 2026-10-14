module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Product.Derived.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Source.Triangulated.Data
public import KIP126.Def.StableHomotopy.InverseSequence.HomotopyLimit.Existence.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory CategoryTheory.Limits

universe u

/-- The Milnor homotopy limit in the original stable category, using its
constructed countable product and actual distinguished triangles. -/
noncomputable def sourceHomotopyLimit (D : InverseSequence SourceCategory.{u}) :
    SourceCategory.{u} := Classical.choose D.exists_homotopyLimit

/-- The actual Milnor triangle, including its two specified structure maps. -/
noncomputable def sourceHomotopyLimitWitness (D : InverseSequence SourceCategory.{u}) :
    SequentialHomotopyLimit D (sourceHomotopyLimit D) :=
  Classical.choice (Classical.choose_spec D.exists_homotopyLimit)

end KIP126.StableHomotopy.Implementation
