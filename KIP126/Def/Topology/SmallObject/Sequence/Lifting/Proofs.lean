module

public import KIP126.Def.Topology.SmallObject.Sequence.Proofs
public import Mathlib.CategoryTheory.LiftingProperties.Limits
public import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting

@[expose] public section

namespace KIP126.Topology.SmallObject

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C] {I : Type w} {A B : I → C}
  (f : ∀ i, A i ⟶ B i) [HasPushouts C]
  [∀ {X S : C} (π : X ⟶ S), HasColimitsOfShape
    (Discrete (CategoryTheory.SmallObject.FunctorObjIndex f π)) C]
  {S : C} (X : Over S) {E T : C} (q : E ⟶ T)

set_option backward.isDefEq.respectTransparency false

/-- A simultaneous attachment of the actual generators has the left lifting
property against every map lifting against those generators. -/
theorem cellularStageMap_hasLiftingProperty
    (hq : ∀ i, HasLiftingProperty (f i) q) (n : ℕ) :
    HasLiftingProperty (cellularStageMap f X n) q := by
  letI := hq
  dsimp only [cellularStageMap, CategoryTheory.SmallObject.ιFunctorObj,
    CategoryTheory.SmallObject.functorObjLeft]
  infer_instance

/-- The actual initial-to-countable-attachment inclusion has the left lifting
property, obtained by compatible lifts through its actual finite stages. -/
theorem cellularReplacement_initial_hasLiftingProperty
    [HasColimit (cellularSequence f X)]
    (hq : ∀ i, HasLiftingProperty (f i) q) :
    HasLiftingProperty (colimit.ι (cellularSequence f X) 0) q := by
  apply HasLiftingProperty.transfiniteComposition.hasLiftingProperty_ι_app_bot
    (colimit.isColimit (cellularSequence f X))
  intro n hn
  simpa only [cellularSequence, Functor.ofSequence_map_homOfLE_succ] using
    cellularStageMap_hasLiftingProperty f X q hq n

end KIP126.Topology.SmallObject
