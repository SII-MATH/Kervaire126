module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Colimit.Bond.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits Topology
open scoped unitInterval

universe u
variable {J : Type u} [Category.{u} J] (F : J ⥤ Prespectrum.{u})

theorem pointwiseColimitBond_point (n : ℕ) (t : I) :
    pointwiseColimitBond F n ((pointwiseColimitLevel F n).point,t) =
      (pointwiseColimitLevel F (n+1)).point :=
  congrArg (fun p => p t) (pointwiseColimitBondAdjoint F n).point

theorem pointwiseColimitBond_zero (n : ℕ) (x : pointwiseColimitLevel F n) :
    pointwiseColimitBond F n (x,0) = (pointwiseColimitLevel F (n+1)).point :=
  Path.source _

theorem pointwiseColimitBond_one (n : ℕ) (x : pointwiseColimitLevel F n) :
    pointwiseColimitBond F n (x,1) = (pointwiseColimitLevel F (n+1)).point :=
  Path.target _

/-- The actual colimit bond restricts to each specified input bond. -/
theorem pointwiseColimitBond_inclusion (n : ℕ) (j : J) (x : (F.obj j).level n) (t : I) :
    pointwiseColimitBond F n ((pointwiseColimitLevelInclusion F n j).map x,t) =
      (pointwiseColimitLevelInclusion F (n+1) j).map ((F.obj j).bond n (x,t)) :=
  congrArg (fun (f : (F.obj j).level n ⟶ loopLevel (pointwiseColimitLevel F (n+1))) =>
    f.map x t) (colimit.ι_desc (pointwiseColimitBondCocone F n) j)

end KIP126.StableHomotopy.Implementation.Prespectrum
