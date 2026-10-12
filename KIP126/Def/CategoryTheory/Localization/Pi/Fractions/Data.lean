module

public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import Mathlib.CategoryTheory.Localization.Pi

@[expose] public section

namespace KIP126.Foundation

open CategoryTheory

universe w u v
variable {J : Type w} {C : J → Type u} [∀ j, Category.{v} (C j)]
  (W : ∀ j, MorphismProperty (C j))

/-- A family of actual right fractions has a single right-fraction shape
in the product category, with its denominator chosen coordinatewise. -/
def piRightFraction {X Y : ∀ j, C j} (φ : ∀ j, (W j).RightFraction (X j) (Y j)) :
    (MorphismProperty.pi W).RightFraction X Y where
  X' j := (φ j).X'
  s j := (φ j).s
  hs j := (φ j).hs
  f j := (φ j).f

def rightFractionComponent {X Y : ∀ j, C j}
    (φ : (MorphismProperty.pi W).RightFraction X Y) (j : J) :
    (W j).RightFraction (X j) (Y j) where
  X' := φ.X' j
  s := φ.s j
  hs := φ.hs j
  f := φ.f j

end KIP126.Foundation
