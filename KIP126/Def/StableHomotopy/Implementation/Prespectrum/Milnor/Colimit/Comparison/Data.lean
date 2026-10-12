module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Milnor.Colimit.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.SequentialHomotopyColimit.Source.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory

universe u

/-- The actual comparison from the Milnor cofiber to the topological
cylinder telescope, induced by the latter's proved compatible source maps. -/
noncomputable def sourceHomotopyColimitToTelescope (F : ℕ ⥤ Prespectrum.{u}) :
    sourceHomotopyColimit (F ⋙ sourceLocalization) ⟶
      sourceLocalization.obj (Prespectrum.sequentialHomotopyColimit F) :=
  (sourceHomotopyColimit_exists_desc (F ⋙ sourceLocalization)
    (fun n => (Prespectrum.sourceSequentialHomotopyColimitCocone F).ι.app n)
    (fun n => (Prespectrum.sourceSequentialHomotopyColimitCocone F).w
      (homOfLE (Nat.le_succ n)))).choose

end KIP126.StableHomotopy.Implementation
