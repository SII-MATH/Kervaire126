module

public import KIP126.Def.Topology.SmallObject.Topological.Proofs
public import KIP126.Def.Topology.HomotopyExtension.Cells.Proofs

@[expose] public section

namespace KIP126.Topology.SmallObject

open CategoryTheory CategoryTheory.Limits HomotopyExtension

universe u v

variable {I : Type v} [Small.{u} I] {A B : I → TopCat.{u}}
  (f : ∀ i, A i ⟶ B i) {S : TopCat.{u}} (X : Over S)

set_option backward.isDefEq.respectTransparency false

/-- Every actual stage inclusion has homotopy extension when all the
specified cell-boundary maps do. -/
theorem cellularStageMap_hasHomotopyExtension
    (hf : ∀ i, HasHomotopyExtension (f i)) (n : ℕ) :
    HasHomotopyExtension (cellularStageMap f X n) :=
  hasHomotopyExtension_of_attachCells
    (CategoryTheory.SmallObject.attachCellsιFunctorObjOfSmall.{u} f (cellularStage f X n).hom) hf

/-- The genuine initial-space inclusion into the countable attachment
has homotopy extension, retaining every prescribed parameter value. -/
theorem cellularInitialInclusion_hasHomotopyExtension
    (hf : ∀ i, HasHomotopyExtension (f i)) :
    HasHomotopyExtension (colimit.ι (cellularSequence f X) 0) := by
  apply (hasHomotopyExtension_iff_lifting _).mpr
  intro Z
  apply HasLiftingProperty.transfiniteComposition.hasLiftingProperty_ι_app_bot
    (colimit.isColimit (cellularSequence f X))
  intro n hn
  change HasLiftingProperty ((cellularSequence f X).map (homOfLE (Nat.le_succ n))) _
  rw [cellularSequence,Functor.ofSequence_map_homOfLE_succ]
  exact (hasHomotopyExtension_iff_lifting _).mp
    (cellularStageMap_hasHomotopyExtension f X hf n) Z

end KIP126.Topology.SmallObject
