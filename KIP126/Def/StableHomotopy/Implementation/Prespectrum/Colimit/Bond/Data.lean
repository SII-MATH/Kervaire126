module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Colimit.Level.Data
public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.Loop.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits Topology
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- Curry the actual bonds, retaining the based path endpoints, to a
cocone on the actual based level diagram. -/
noncomputable def pointwiseColimitBondCocone {J : Type u} [Category.{u} J]
    (F : J ⥤ Prespectrum.{u}) (n : ℕ) : Cocone (F ⋙ evaluationFunctor n) where
  pt := loopLevel (pointwiseColimitLevel F (n+1))
  ι :=
    { app := fun j =>
        BasedSpace.basedLoopCurry ((F.obj j).bond n)
          ((F.obj j).bond_point n) ((F.obj j).bond_zero n) ((F.obj j).bond_one n) ≫
        BasedSpace.basedLoopMap (pointwiseColimitLevelInclusion F (n+1) j)
      naturality := by
        intro j k h
        apply BasedSpace.Hom.ext
        apply ContinuousMap.ext
        intro x
        apply Path.ext
        funext t
        change (pointwiseColimitLevelInclusion F (n+1) k).map
          ((F.obj k).bond n ((F.map h).level n x,t)) =
            (pointwiseColimitLevelInclusion F (n+1) j).map ((F.obj j).bond n (x,t))
        rw [← (F.map h).bond n x t]
        exact congrArg (fun g => g.map ((F.obj j).bond n (x,t)))
          (colimit.w (F ⋙ evaluationFunctor (n+1)) h) }

noncomputable def pointwiseColimitBondAdjoint {J : Type u} [Category.{u} J]
    (F : J ⥤ Prespectrum.{u}) (n : ℕ) :
    pointwiseColimitLevel F n ⟶ loopLevel (pointwiseColimitLevel F (n+1)) :=
  colimit.desc (F ⋙ evaluationFunctor n) (pointwiseColimitBondCocone F n)

/-- The genuine continuous structure map obtained from based path evaluation. -/
noncomputable def pointwiseColimitBond {J : Type u} [Category.{u} J]
    (F : J ⥤ Prespectrum.{u}) (n : ℕ) :
    C(pointwiseColimitLevel F n × I, pointwiseColimitLevel F (n+1)) where
  toFun z := (pointwiseColimitBondAdjoint F n).map z.1 z.2
  continuous_toFun := continuous_eval.comp
    (((pointwiseColimitBondAdjoint F n).map.continuous.comp continuous_fst).prodMk
      continuous_snd)

end KIP126.StableHomotopy.Implementation.Prespectrum
