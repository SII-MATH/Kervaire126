module

public import KIP126.Def.StableHomotopy.Context.TensorSuspension.Braiding.Proofs

@[expose] public section


namespace KIP126.StableHomotopy
open CategoryTheory MonoidalCategory BraidedCategory
universe u v
variable {C : Type u} [StableHomotopyCategory.{u,v} C] [BraidedCategory C]
  [right : ∀ X : C, (tensorRight X).CommShift ℤ]
  [left : ∀ X : C, (tensorLeft X).CommShift ℤ]

set_option backward.isDefEq.respectTransparency false

/-- This coherence is a consequence of the actual left-shift construction,
not a new compatibility premise on the Adams pairing. -/
theorem tensorSuspensionBraidingCompatibility_of_leftShift_eq
    (h : ∀ X : C, left X =
      Functor.CommShift.ofIso (tensorLeftIsoTensorRight X).symm ℤ) :
    TensorSuspensionBraidingCompatibility (C := C) := by
  have hl : left = fun X =>
      Functor.CommShift.ofIso (tensorLeftIsoTensorRight X).symm ℤ := funext h
  cases hl
  intro X B
  letI : (tensorLeft X).CommShift ℤ :=
    Functor.CommShift.ofIso (tensorLeftIsoTensorRight X).symm ℤ
  letI : NatTrans.CommShift (tensorLeftIsoTensorRight X).symm.hom ℤ :=
    Functor.CommShift.ofIso_compatibility (tensorLeftIsoTensorRight X).symm ℤ
  have hi := NatTrans.shift_app_comm (tensorLeftIsoTensorRight X).symm.inv (1 : ℤ) B
  exact hi.symm

end KIP126.StableHomotopy
