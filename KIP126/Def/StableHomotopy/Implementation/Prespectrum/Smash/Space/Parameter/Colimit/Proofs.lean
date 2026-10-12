module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Parameter.Colimit.Data
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Limits
universe v w

/-- With any actual spectrum fixed, its space parameter smash
preserves the original colimit of any compactly generated diagram. -/
instance spaceSmashParameterFunctor_preservesColimit
    {J : Type v} [Category.{w} J] (F : J ⥤ BasedSpace.{0})
    [HasColimit F] [∀ j, UCompactlyGeneratedSpace.{0} (F.obj j)]
    (X : Prespectrum.{0}) : PreservesColimit F (spaceSmashParameterFunctor X) :=
  preservesColimit_of_preserves_colimit_cocone (colimit.isColimit F)
    (spaceSmashParameter_mapCocone_isColimit F (colimit.cocone F) (colimit.isColimit F) X)

/-- Actual parameter pushouts remain actual strict spectrum pushouts.
In particular the original attaching maps and quotient object are kept. -/
theorem spaceSmashParameter_isPushout
    {A B C D : BasedSpace.{0}} [UCompactlyGeneratedSpace.{0} A]
    [UCompactlyGeneratedSpace.{0} B] [UCompactlyGeneratedSpace.{0} C]
    {a : A ⟶ B} {b : A ⟶ C} {i : B ⟶ D} {j : C ⟶ D}
    (h : IsPushout a b i j) (X : Prespectrum.{0}) :
    IsPushout (spaceSmashMap a (𝟙 X)) (spaceSmashMap b (𝟙 X))
      (spaceSmashMap i (𝟙 X)) (spaceSmashMap j (𝟙 X)) := by
  letI (k : WalkingSpan) : UCompactlyGeneratedSpace.{0} ((span a b).obj k) := by
    cases k with
    | none => exact inferInstanceAs (UCompactlyGeneratedSpace.{0} A)
    | some k =>
      cases k with
      | left => exact inferInstanceAs (UCompactlyGeneratedSpace.{0} B)
      | right => exact inferInstanceAs (UCompactlyGeneratedSpace.{0} C)
  exact h.map (spaceSmashParameterFunctor X)

end KIP126.StableHomotopy.Implementation.Prespectrum
