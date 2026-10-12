module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.CellularCover.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Functor.Coproduct.Vanishing.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Sphere.Source.Connectivity.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false

/-- Every original stable class is hit by its own actual sphere summand. -/
theorem sourceSphereCoverMap_surjective (X : SourceCategory.{0}) (n : ℤ) :
    Function.Surjective ((sourceStableHomotopyAddFunctor n).map (sourceSphereCoverMap X n)) := by
  let F := sourceStableHomotopyAddFunctor n
  let A (_ : F.obj X) := Prespectrum.sourceSphere n
  intro x
  refine ⟨F.map (Sigma.ι A x) (Prespectrum.sourceSphereGenerator n),?_⟩
  change (F.map (Sigma.ι A x) ≫ F.map (sourceSphereCoverMap X n))
    (Prespectrum.sourceSphereGenerator n) = x
  rw [← F.map_comp]
  simp only [sourceSphereCoverMap, Sigma.ι_desc]
  change (forget AddCommGrpCat).map ((sourceStableHomotopyAddFunctor n).map
    (Prespectrum.sourceStableHomotopyEquiv X.as.obj n x)) (Prespectrum.sourceSphereGenerator n) = x
  rw [sourceStableHomotopyAddFunctor_forget_map]
  exact Prespectrum.stableHomotopySourceMap_generator_image X.as.obj n x

/-- The actual sphere cover retains its specified lower connectivity bound. -/
theorem sourceSphereCover_homotopy_subsingleton (X : SourceCategory.{0}) (n d : ℤ)
    (hd : d < n) : Subsingleton ((sourceStableHomotopyAddFunctor d).obj (sourceSphereCover X n)) :=
  sourceCoproduct_homotopy_subsingleton _ d
    (fun _ => Prespectrum.sourceSphere_homotopy_subsingleton n d hd)

end KIP126.StableHomotopy.Implementation
