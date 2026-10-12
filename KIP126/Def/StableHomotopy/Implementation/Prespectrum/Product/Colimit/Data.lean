module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Product.Proofs
public import KIP126.Def.Algebra.Colimit.FiniteProduct
public import KIP126.Def.Algebra.Colimit.Map.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

universe u

variable {J : Type}

/-- Project the actual stable classes to the stable classes of the factors. -/
def stablePiComparison (X : J → Prespectrum.{u}) (d : ℤ) :
    StableHomotopy (piPrespectrum X) d → ∀ j, StableHomotopy (X j) d :=
  fun x j => stableHomotopyMap (piProjection X j) d x

/-- Compare the level-group colimit of the actual product with the colimit
of the pointwise product of the actual level-group systems. -/
noncomputable def stablePiColimitMap (X : J → Prespectrum.{u}) (d : ℤ) :
    stableGroupColimit (piPrespectrum X) d →
      _root_.DirectLimit (fun k => ∀ j, stableLevelGroup (X j) d k)
        (KIP126.Core.DirectLimit.piTransition (fun j => stableLevelGroup (X j) d)
          (fun j => stableLevelTransition (X j) d)) :=
  _root_.DirectLimit.map (stableLevelTransition (piPrespectrum X) d)
    (KIP126.Core.DirectLimit.piTransition (fun j => stableLevelGroup (X j) d)
      (fun j => stableLevelTransition (X j) d))
    (fun k => levelPiComparison X (stableGroupStage d k) (stableGroupDimension d k))
    (fun i k h x => funext fun j => (stableLevelPiComparison_transition X d i k h x j).symm)

/-- The same comparison expressed in the direct-limit coordinates of every factor. -/
noncomputable def stablePiColimitCode (X : J → Prespectrum.{u}) (d : ℤ)
    (x : StableHomotopy (piPrespectrum X) d) : ∀ j, stableGroupColimit (X j) d :=
  KIP126.Core.DirectLimit.piComparison (fun j => stableLevelGroup (X j) d)
    (fun j => stableLevelTransition (X j) d) (stablePiColimitMap X d (stableGroupCode _ d x))

end KIP126.StableHomotopy.Implementation.Prespectrum
