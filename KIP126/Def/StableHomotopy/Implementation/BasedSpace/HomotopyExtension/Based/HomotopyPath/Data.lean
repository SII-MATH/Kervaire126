module

public import KIP126.Def.StableHomotopy.Implementation.Generators

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.BasedSpace

open CategoryTheory
open scoped unitInterval

universe u

/-- The actual compact-open free path space, pointed by the constant path
at the specified original point. -/
abbrev homotopyPathSpace (X : BasedSpace.{u}) : BasedSpace.{u} where
  space := TopCat.of C(I,X)
  point := ContinuousMap.const _ X.point

/-- Evaluation at the initial endpoint in the original based path space. -/
def homotopyPathEvaluationZero (X : BasedSpace.{u}) : homotopyPathSpace X ⟶ X where
  map := ⟨fun p => p 0, continuous_eval_const _⟩
  point := rfl

end KIP126.StableHomotopy.Implementation.BasedSpace
