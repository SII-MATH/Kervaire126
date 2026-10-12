module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Product.Proofs
public import Mathlib.CategoryTheory.Pi.Basic

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

universe u

set_option backward.isDefEq.respectTransparency false

/-- The actual pointwise product as a functor of indexed prespectrum families. -/
def piPrespectrumFunctor (J : Type) : (J → Prespectrum.{u}) ⥤ Prespectrum.{u} where
  obj := piPrespectrum
  map := piMap
  map_id X := by
    apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro x
    rfl
  map_comp f g := by
    apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro x
    rfl

end KIP126.StableHomotopy.Implementation.Prespectrum
