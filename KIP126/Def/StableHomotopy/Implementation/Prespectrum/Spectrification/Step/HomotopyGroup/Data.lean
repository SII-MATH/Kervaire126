module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Spectrification.Currying.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
universe u

/-- First-coordinate currying is an actual equivalence of the based
cubical homotopy quotients, including the zero-dimensional quotient. -/
def loopFirstHomotopyEquiv (A : BasedSpace.{u}) (r : ℕ) :
    _root_.HomotopyGroup (Fin r) (loopLevel A) (loopLevel A).point ≃
      _root_.HomotopyGroup (Fin (r+1)) A A.point where
  toFun := Quotient.map (loopUncurryFirst A r)
    (fun _ _ h => ⟨loopUncurryFirstHomotopy A r h.some⟩)
  invFun := Quotient.map (loopCurryFirst A r)
    (fun _ _ h => ⟨loopCurryFirstHomotopy A r h.some⟩)
  left_inv := by
    intro x
    induction x using Quotient.inductionOn with
    | h p => exact congrArg Quotient.mk' (loopCurryFirst_uncurry A r p)
  right_inv := by
    intro x
    induction x using Quotient.inductionOn with
    | h p => exact congrArg Quotient.mk' (loopUncurryFirst_curry A r p)

end KIP126.StableHomotopy.Implementation.Prespectrum
