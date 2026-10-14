module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Cofinal.Even.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
universe u

/-- The actual even-stage stable quotient is equivalent to the original
stable quotient. Forward forgets evenness; inverse advances only odd stages. -/
def evenStableHomotopyEquiv (P : Prespectrum.{u}) (d : ℤ) :
    EvenStableHomotopy P d ≃ StableHomotopy P d where
  toFun := Quot.lift (fun a => Quot.mk _ a.val)
    (fun _ _ h => h.forget_sound)
  invFun := Quot.lift (fun a => Quot.mk _ a.toEven)
    (fun _ _ h => Representative.toEven_relation h)
  left_inv z := by
    induction z using Quot.inductionOn with
    | h a => change Quot.mk _ a.val.toEven = Quot.mk _ a; rw [a.toEven_val]
  right_inv z := by
    induction z using Quot.inductionOn with
    | h a => exact a.toEven_forget

end KIP126.StableHomotopy.Implementation.Prespectrum
