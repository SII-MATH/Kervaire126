module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Milnor.Colimit.Comparison.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory

universe u

/-- The chosen Milnor-to-telescope comparison retains every specified
original stage inclusion exactly. -/
@[reassoc (attr := simp)]
theorem sourceHomotopyColimitToTelescope_inclusion (F : ℕ ⥤ Prespectrum.{u}) (n : ℕ) :
    sourceHomotopyColimitInclusion (F ⋙ sourceLocalization) n ≫
      sourceHomotopyColimitToTelescope F =
        (Prespectrum.sourceSequentialHomotopyColimitCocone F).ι.app n :=
  (sourceHomotopyColimit_exists_desc (F ⋙ sourceLocalization)
    (fun n => (Prespectrum.sourceSequentialHomotopyColimitCocone F).ι.app n)
    (fun n => (Prespectrum.sourceSequentialHomotopyColimitCocone F).w
      (homOfLE (Nat.le_succ n)))).choose_spec n

end KIP126.StableHomotopy.Implementation
