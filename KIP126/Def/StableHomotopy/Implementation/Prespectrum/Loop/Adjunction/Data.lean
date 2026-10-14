module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Adjunction.Hom.Proofs
public import Mathlib.CategoryTheory.Adjunction.Basic

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u

/-- The ordinary reduced-suspension / compact-open-based-loop adjunction,
including the strict prespectrum structure maps. -/
def suspensionLoopAdjunction : suspensionFunctor.{u} ⊣ loopFunctor :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ =>
        { toFun := suspensionLoopCurry
          invFun := suspensionLoopUncurry
          left_inv := suspensionLoopUncurry_curry
          right_inv := suspensionLoopCurry_uncurry }
      homEquiv_naturality_left_symm := suspensionLoopUncurry_natural_left
      homEquiv_naturality_right := suspensionLoopCurry_natural_right }

end KIP126.StableHomotopy.Implementation.Prespectrum
