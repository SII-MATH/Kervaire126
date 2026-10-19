module

public import KIP126.Def.StableHomotopy.Implementation.Sphere.Source.Data
public import KIP126.Def.StableHomotopy.Implementation.Sphere.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Zero.Instances

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
set_option backward.isDefEq.respectTransparency false

/-- Negative representing spheres are precisely the actual padded point-set sphere. -/
theorem sourceSpherePrespectrum_negSucc (n : ℕ) :
    sourceSpherePrespectrum (Int.negSucc n) = (desuspension^[n+1]) sphere := by
  change (desuspension^[n+1]) (suspensionSpectrum BasedSpace.zeroSphere) = _
  rw [suspensionSpectrum_zeroSphere]

/-- Actual sphere connectivity gives uniqueness of every negative-degree ordinary source sphere morphism. No completion model is used. -/
theorem sourceSphere_hom_sourceSphere_zero_subsingleton (d : ℤ) (hd : d < 0) :
    Subsingleton (sourceSphere d ⟶ sourceSphere 0) := by
  rw [sourceSphere_zero]
  letI := sphere_stableHomotopy_subsingleton_of_neg d hd
  exact sourceSphere_hom_subsingleton_of_stableHomotopy_subsingleton sphere d

/-- Every negative-degree morphism of the ordinary source sphere is the
actual categorical zero morphism. -/
theorem sourceSphere_hom_sourceSphere_zero_eq_zero (d : ℤ) (hd : d < 0)
    (f : sourceSphere d ⟶ sourceSphere 0) : f = 0 := by
  letI := sourceSphere_hom_sourceSphere_zero_subsingleton d hd
  exact Subsingleton.elim _ _

end KIP126.StableHomotopy.Implementation.Prespectrum
