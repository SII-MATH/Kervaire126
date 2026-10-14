module

public import KIP126.Def.Topology.SmallObject.Topological.Proofs
public import KIP126.Def.Topology.Colimit.CompactlyGenerated.Proofs

@[expose] public section

namespace KIP126.Topology.SmallObject

open CategoryTheory CategoryTheory.Limits

universe u v

variable {I : Type v} [Small.{u} I] {A B : I → TopCat.{u}}
  (f : ∀ i, A i ⟶ B i) {S : TopCat.{u}} (X : Over S)
  [UCompactlyGeneratedSpace.{u} X.left] [∀ i, UCompactlyGeneratedSpace.{u} (B i)]

set_option backward.isDefEq.respectTransparency false

/-- Every actual small-object stage is compactly generated. -/
theorem cellularStage_uCompactlyGeneratedSpace (n : ℕ) :
    UCompactlyGeneratedSpace.{u} (cellularStage f X n).left := by
  induction n with
  | zero => exact ‹UCompactlyGeneratedSpace.{u} X.left›
  | succ n ih =>
    letI := ih
    exact uCompactlyGeneratedSpace_of_attachCells
      (CategoryTheory.SmallObject.attachCellsιFunctorObjOfSmall.{u} f (cellularStage f X n).hom)

/-- Compact generation holds for the genuine countable attachment
object itself, using its original colimit topology. -/
theorem cellularReplacement_uCompactlyGeneratedSpace :
    UCompactlyGeneratedSpace.{u} (cellularReplacement (C := TopCat.{u}) f X) := by
  letI (n : ℕ) : UCompactlyGeneratedSpace.{u} ((cellularSequence f X).obj n) :=
    cellularStage_uCompactlyGeneratedSpace f X n
  exact uCompactlyGeneratedSpace_of_isColimit (cellularSequence f X) _ (colimit.isColimit _)

end KIP126.Topology.SmallObject
