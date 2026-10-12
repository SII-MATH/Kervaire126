module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.SequentialColimit.Level.Proofs
public import Mathlib.Topology.ContinuousMap.Compact

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- The actual bonds curry to a compatible cocone into the compact-open
space of paths in the next topological colimit level. -/
noncomputable def sequentialColimitBondCocone (F : ℕ ⥤ Prespectrum.{u}) (n : ℕ) :
    Cocone (sequentialLevelDiagram F n) where
  pt := TopCat.of C(I, sequentialColimitLevel F (n+1))
  ι :=
    { app := fun k => TopCat.ofHom
        (((sequentialColimitLevelInclusion F (n+1) k).comp ((F.obj k).bond n)).curry)
      naturality := fun k l h => by
        apply ConcreteCategory.hom_ext
        intro x
        apply ContinuousMap.ext
        intro t
        change sequentialColimitLevelInclusion F (n+1) l
          ((F.obj l).bond n ((F.map h).level n x, t)) =
            sequentialColimitLevelInclusion F (n+1) k ((F.obj k).bond n (x, t))
        rw [← (F.map h).bond n x t]
        exact sequentialColimitLevelInclusion_map F (n+1) h _ }

/-- The genuine continuous bond on the actual level colimits. -/
noncomputable def sequentialColimitBond (F : ℕ ⥤ Prespectrum.{u}) (n : ℕ) :
    C(sequentialColimitLevel F n × I, sequentialColimitLevel F (n+1)) :=
  ((colimit.desc (sequentialLevelDiagram F n) (sequentialColimitBondCocone F n)).hom).uncurry

end KIP126.StableHomotopy.Implementation.Prespectrum
