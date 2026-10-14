module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.SequentialHomotopyColimit.Stages
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.SequentialColimit.Separation.Proofs

@[expose] public section

section

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

end

section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory _root_.Topology

universe u

set_option backward.isDefEq.respectTransparency false

/-- The actual comparison is a stable equivalence at each original stage. -/
theorem sequentialHomotopyComparison_stableEquivalence (F : ℕ ⥤ Prespectrum.{u}) (k : ℕ) :
    stableEquivalences ((sequentialHomotopyComparison F).app k) := by
  intro d
  change Function.Bijective ((stableHomotopyFunctor d).map
    ((sequentialCylinderProjection (F ⋙ cubicalReplacementFunctor)).app k ≫
      cubicalReplacementComparison.app (F.obj k)))
  rw [CategoryTheory.Functor.map_comp]
  exact (cubicalReplacementComparison_stableEquivalence (F.obj k) d).comp
    (sequentialCylinderProjection_stableEquivalence (F ⋙ cubicalReplacementFunctor) k d)

instance sequentialHomotopyDiagram_level_t1Space (F : ℕ ⥤ Prespectrum.{u}) (k n : ℕ) :
    T1Space (((sequentialHomotopyDiagram F).obj k).level n) := by
  letI (k n : ℕ) : T1Space (((F ⋙ cubicalReplacementFunctor).obj k).level n) :=
    cubicalReplacementFunctor_level_t1Space (F.obj k) n
  exact sequentialCylinderStage_level_t1Space (F ⋙ cubicalReplacementFunctor) k n

/-- The telescope transitions are genuine closed embeddings for every
original strict sequence, due to its constructed T1 replacement. -/
theorem sequentialHomotopyDiagram_successor_closed (F : ℕ ⥤ Prespectrum.{u}) (k n : ℕ) :
    IsClosedEmbedding (((sequentialHomotopyDiagram F).map
      (homOfLE (Nat.le_succ k))).level n) := by
  letI (k n : ℕ) : T1Space (((F ⋙ cubicalReplacementFunctor).obj k).level n) :=
    cubicalReplacementFunctor_level_t1Space (F.obj k) n
  exact sequentialCylinderDiagram_successor_closed (F ⋙ cubicalReplacementFunctor) k n

instance sequentialHomotopyColimit_level_t1Space (F : ℕ ⥤ Prespectrum.{u}) (n : ℕ) :
    T1Space ((sequentialHomotopyColimit F).level n) :=
  sequentialColimit_level_t1Space (sequentialHomotopyDiagram F)
    (sequentialHomotopyDiagram_successor_closed F) n

end KIP126.StableHomotopy.Implementation.Prespectrum

end
