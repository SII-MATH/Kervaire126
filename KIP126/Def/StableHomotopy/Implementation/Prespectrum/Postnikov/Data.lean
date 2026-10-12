module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.CellularCover.Upper.Cofiber.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Milnor.Colimit.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory

/-- Iterated actual cofibers of the upper sphere covers, starting at the
specified source object. -/
noncomputable def sourcePostnikovStage (X : SourceCategory.{0}) (n : ℤ) : ℕ → SourceCategory.{0}
  | 0 => X
  | k+1 => sourceUpperCellKilling (sourcePostnikovStage X n k) n

/-- The original cofiber maps between consecutive stages. -/
noncomputable def sourcePostnikovStageMap (X : SourceCategory.{0}) (n : ℤ) (k : ℕ) :
    sourcePostnikovStage X n k ⟶ sourcePostnikovStage X n (k+1) :=
  sourceUpperCellKillingUnit (sourcePostnikovStage X n k) n

/-- The actual source sequence of repeated upper-cell killing. -/
noncomputable def sourcePostnikovDiagram (X : SourceCategory.{0}) (n : ℤ) :
    ℕ ⥤ SourceCategory.{0} := Functor.ofSequence (sourcePostnikovStageMap X n)

/-- The constructed truncation below n is the actual Milnor homotopy
colimit of the specified upper-cell-killing sequence. -/
noncomputable def sourcePostnikovTruncation (X : SourceCategory.{0}) (n : ℤ) :
    SourceCategory.{0} := sourceHomotopyColimit (sourcePostnikovDiagram X n)

/-- The original zero-stage inclusion gives the actual truncation unit. -/
noncomputable def sourcePostnikovUnit (X : SourceCategory.{0}) (n : ℤ) :
    X ⟶ sourcePostnikovTruncation X n :=
  sourceHomotopyColimitInclusion (sourcePostnikovDiagram X n) 0

end KIP126.StableHomotopy.Implementation
