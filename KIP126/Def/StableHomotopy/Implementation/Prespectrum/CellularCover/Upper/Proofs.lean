module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.CellularCover.Upper.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.CellularCover.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false

/-- The actual upper sphere cover is surjective in each of its specified degrees. -/
theorem sourceUpperSphereCoverMap_surjective (X : SourceCategory.{0}) (n d : ℤ) (hd : n ≤ d) :
    Function.Surjective ((sourceStableHomotopyAddFunctor d).map (sourceUpperSphereCoverMap X n)) := by
  let F := sourceStableHomotopyAddFunctor d
  let A (a : SourceUpperSphereIndex X n) := Prespectrum.sourceSphere a.1.val
  intro x
  let a : SourceUpperSphereIndex X n := ⟨⟨d,hd⟩,x⟩
  refine ⟨F.map (Sigma.ι A a) (Prespectrum.sourceSphereGenerator d),?_⟩
  change (F.map (Sigma.ι A a) ≫ F.map (sourceUpperSphereCoverMap X n))
    (Prespectrum.sourceSphereGenerator d) = x
  rw [← F.map_comp]
  simp only [sourceUpperSphereCoverMap, Sigma.ι_desc]
  change (forget AddCommGrpCat).map ((sourceStableHomotopyAddFunctor d).map
    (Prespectrum.sourceStableHomotopyEquiv X.as.obj d x)) (Prespectrum.sourceSphereGenerator d) = x
  rw [sourceStableHomotopyAddFunctor_forget_map]
  exact Prespectrum.stableHomotopySourceMap_generator_image X.as.obj d x

/-- Its actual stable groups vanish in every degree below the chosen bound. -/
theorem sourceUpperSphereCover_homotopy_subsingleton (X : SourceCategory.{0}) (n d : ℤ)
    (hd : d < n) :
    Subsingleton ((sourceStableHomotopyAddFunctor d).obj (sourceUpperSphereCover X n)) :=
  sourceCoproduct_homotopy_subsingleton _ d
    (fun a => Prespectrum.sourceSphere_homotopy_subsingleton a.1.val d (lt_of_lt_of_le hd a.1.property))

end KIP126.StableHomotopy.Implementation
