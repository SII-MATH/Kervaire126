module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Source.Group.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

universe u

/-- Every localized hom set into an actual loop object has its actual
concatenation group, including morphisms represented by zigzags. -/
@[implicit_reducible]
noncomputable def sourceLoopHomGroup (X : Prespectrum.{u}) (A : SourceCategory.{u}) :
    AddGroup (A ⟶ sourceLocalization.obj (Prespectrum.loop X)) := by
  letI : Add (A ⟶ sourceLocalization.obj (Prespectrum.loop X)) := ⟨sourceLoopAdd X⟩
  letI : Neg (A ⟶ sourceLocalization.obj (Prespectrum.loop X)) := ⟨sourceLoopNeg X⟩
  exact {
  add := sourceLoopAdd X
  zero := 0
  neg := sourceLoopNeg X
  add_assoc := sourceLoopAdd_assoc X
  zero_add := zero_sourceLoopAdd X
  add_zero := sourceLoopAdd_zero X
  neg_add_cancel := sourceLoopNeg_add X
  nsmul := nsmulRec
  zsmul := zsmulRec }

end KIP126.StableHomotopy.Implementation.Prespectrum
