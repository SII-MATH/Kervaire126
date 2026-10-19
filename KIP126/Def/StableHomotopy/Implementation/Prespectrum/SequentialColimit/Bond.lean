module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.SequentialColimit.Level
public import Mathlib.Topology.ContinuousMap.Compact

@[expose] public section

section

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

end

section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- The actual colimit bond agrees exactly with each original stage bond. -/
theorem sequentialColimitBond_inclusion (F : ℕ ⥤ Prespectrum.{u}) (n k : ℕ)
    (x : (F.obj k).level n) (t : I) :
    sequentialColimitBond F n (sequentialColimitLevelInclusion F n k x, t) =
      sequentialColimitLevelInclusion F (n+1) k ((F.obj k).bond n (x, t)) :=
  congrArg (fun f : C(I, sequentialColimitLevel F (n+1)) => f t)
    (ConcreteCategory.congr_hom
      (colimit.ι_desc (sequentialColimitBondCocone F n) k) x)

theorem sequentialColimitBond_point (F : ℕ ⥤ Prespectrum.{u}) (n : ℕ) (t : I) :
    sequentialColimitBond F n ((sequentialColimitLevel F n).point, t) =
      (sequentialColimitLevel F (n+1)).point := by
  change sequentialColimitBond F n
    (sequentialColimitLevelInclusion F n 0 ((F.obj 0).level n).point, t) = _
  rw [sequentialColimitBond_inclusion, (F.obj 0).bond_point]
  rfl

theorem sequentialColimitBond_zero (F : ℕ ⥤ Prespectrum.{u}) (n : ℕ)
    (x : sequentialColimitLevel F n) :
    sequentialColimitBond F n (x, 0) = (sequentialColimitLevel F (n+1)).point := by
  obtain ⟨k, y, rfl⟩ := sequentialColimitLevelInclusion_jointly_surjective F n x
  rw [sequentialColimitBond_inclusion, (F.obj k).bond_zero, sequentialColimitLevelInclusion_point]

theorem sequentialColimitBond_one (F : ℕ ⥤ Prespectrum.{u}) (n : ℕ)
    (x : sequentialColimitLevel F n) :
    sequentialColimitBond F n (x, 1) = (sequentialColimitLevel F (n+1)).point := by
  obtain ⟨k, y, rfl⟩ := sequentialColimitLevelInclusion_jointly_surjective F n x
  rw [sequentialColimitBond_inclusion, (F.obj k).bond_one, sequentialColimitLevelInclusion_point]

end KIP126.StableHomotopy.Implementation.Prespectrum

end
