module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.SequentialHomotopyColimit.Stages.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

universe u

/-- The actual closed-cylinder sequence obtained after applying the proved
functorial free-cell replacement to every object of a strict sequence. -/
noncomputable def sequentialHomotopyDiagram (F : ℕ ⥤ Prespectrum.{u}) : ℕ ⥤ Prespectrum.{u} :=
  sequentialCylinderDiagram (F ⋙ cubicalReplacementFunctor)

/-- The actual natural comparison to the original strict sequence. -/
noncomputable def sequentialHomotopyComparison (F : ℕ ⥤ Prespectrum.{u}) :
    sequentialHomotopyDiagram F ⟶ F :=
  sequentialCylinderProjection (F ⋙ cubicalReplacementFunctor) ≫
    Functor.whiskerLeft F cubicalReplacementComparison

/-- The actual topological telescope of an arbitrary strict prespectrum
sequence. No separation or embedding hypotheses are imposed on its input. -/
noncomputable def sequentialHomotopyColimit (F : ℕ ⥤ Prespectrum.{u}) : Prespectrum.{u} :=
  sequentialColimit (sequentialHomotopyDiagram F)

end KIP126.StableHomotopy.Implementation.Prespectrum
