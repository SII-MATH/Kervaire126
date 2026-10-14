module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Equivalence.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u

/-- Actual pointwise loops preserve the originally specified stable equivalences. -/
theorem loopMap_stableEquivalence {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (hf : stableEquivalences f) : stableEquivalences (loopMap f) := by
  intro d
  have h : stableHomotopyMap (loopMap f) d =
      (stableLoopHomotopyEquiv Y d).symm ∘ stableHomotopyMap f (d+1) ∘
        stableLoopHomotopyEquiv X d := by
    funext x
    apply (stableLoopHomotopyEquiv Y d).injective
    exact (stableLoopHomotopyMap_natural f d x).trans
      ((stableLoopHomotopyEquiv Y d).apply_symm_apply _).symm
  rw [h]
  exact (stableLoopHomotopyEquiv Y d).symm.bijective.comp
    ((hf (d+1)).comp (stableLoopHomotopyEquiv X d).bijective)

end KIP126.StableHomotopy.Implementation.Prespectrum
