module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Preadditive.Hom.Proofs
public import KIP126.Def.CategoryTheory.Preadditive.Bilinear.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

universe u

/-- The original ordinary stable localization is preadditive, with addition
constructed from actual path concatenation and the proved loop equivalence. -/
noncomputable instance sourcePreadditive : Preadditive SourceCategory.{u} := by
  letI := sourceHomGroup
  exact KIP126.Foundation.preadditiveOfBilinearHomGroups
    sourceHomGroup_add_comp sourceHomGroup_comp_add

end KIP126.StableHomotopy.Implementation.Prespectrum
