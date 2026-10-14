module

public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.HomotopyExtension.Based.Predicates
public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.HomotopyExtension.Based.HomotopyPath.Data
public import Mathlib.CategoryTheory.LiftingProperties.Limits
public import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.BasedSpace

open CategoryTheory CategoryTheory.Limits
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- Based homotopy extension is the lifting property against the actual
based free-path evaluation, with its constant base path. -/
theorem hasBasedHomotopyExtension_iff_lifting {A B : BasedSpace.{u}} (i : A ⟶ B) :
    HasBasedHomotopyExtension i ↔ ∀ Z : BasedSpace.{u},
      HasLiftingProperty i (homotopyPathEvaluationZero Z) := by
  constructor
  · intro h Z
    constructor
    intro p f sq
    obtain ⟨H,hHp,hH0,hHi⟩ := h Z f p.map.uncurry
      (fun t => congrArg (fun q : C(I,Z) => q t) p.point)
      (fun a => congrArg (fun q : A ⟶ Z => q.map a) sq.w)
    exact CommSq.HasLift.mk' {
      l := ⟨H.curry, by ext t; exact hHp t⟩
      fac_left := by
        apply Hom.ext
        apply ContinuousMap.ext
        intro a
        apply ContinuousMap.ext
        intro t
        exact hHi a t
      fac_right := by
        apply Hom.ext
        apply ContinuousMap.ext
        intro b
        exact hH0 b }
  · intro h Z f p hp h0
    letI := h Z
    let q : A ⟶ homotopyPathSpace Z := ⟨p.curry, by ext t; exact hp t⟩
    let sq : CommSq q i (homotopyPathEvaluationZero Z) f :=
      ⟨by
        apply Hom.ext
        apply ContinuousMap.ext
        intro a
        exact h0 a⟩
    refine ⟨sq.lift.map.uncurry, ?_, ?_, ?_⟩
    · intro t
      exact congrArg (fun r : C(I,Z) => r t) sq.lift.point
    · intro b
      exact congrArg (fun q : B ⟶ Z => q.map b) sq.fac_right
    · intro a t
      exact congrArg (fun q : A ⟶ homotopyPathSpace Z => q.map a t) sq.fac_left

/-- An actual based pushout preserves based homotopy extension. -/
theorem hasBasedHomotopyExtension_of_isPushout {A B C D : BasedSpace.{u}}
    {f : A ⟶ B} {g : A ⟶ C} {i : B ⟶ D} {j : C ⟶ D}
    (h : IsPushout f g i j) (hf : HasBasedHomotopyExtension f) :
    HasBasedHomotopyExtension j := by
  apply (hasBasedHomotopyExtension_iff_lifting j).mpr
  intro Z
  letI := (hasBasedHomotopyExtension_iff_lifting f).mp hf Z
  exact h.flip.hasLiftingProperty (homotopyPathEvaluationZero Z)

/-- Actual coproduct maps preserve based homotopy extension, with every
original summand and both specified colimit cofans retained. -/
theorem hasBasedHomotopyExtension_of_coproduct
    {ι : Type u} {A B : ι → BasedSpace.{u}} (f : ∀ i, A i ⟶ B i)
    (hf : ∀ i, HasBasedHomotopyExtension (f i))
    (cA : Cofan A) (cB : Cofan B) (hA : IsColimit cA) (hB : IsColimit cB)
    (m : cA.pt ⟶ cB.pt) (hm : ∀ i, cA.inj i ≫ m = f i ≫ cB.inj i) :
    HasBasedHomotopyExtension m := by
  apply (hasBasedHomotopyExtension_iff_lifting m).mpr
  intro Z
  let W := MorphismProperty.ofHoms f
  have hp : W.rlp (homotopyPathEvaluationZero Z) := by
    intro S T j hj
    cases hj with
    | mk a => exact (hasBasedHomotopyExtension_iff_lifting _).mp (hf a) Z
  have hc : W.colimitsOfShape (Discrete ι) m :=
    MorphismProperty.colimitsOfShape.mk' _ _ _ _ hA hB
      (Discrete.natTrans (fun a => f a.as)) (fun ⟨a⟩ => MorphismProperty.ofHoms.mk a) m
      (fun ⟨a⟩ => hm a)
  exact W.colimitsOfShape_discrete_le_llp_rlp ι m hc (homotopyPathEvaluationZero Z) hp

end KIP126.StableHomotopy.Implementation.BasedSpace
