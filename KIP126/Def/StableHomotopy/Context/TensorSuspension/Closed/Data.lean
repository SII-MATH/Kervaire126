module

public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

@[expose] public section


/-! The original closed-tensor adjunctions and their ordinary associator mates.
No shift structure or family compatibility is chosen here. -/
namespace KIP126.StableHomotopy.TensorShift
open CategoryTheory MonoidalCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]

/-- The ordinary natural currying iso, defined by mates of the actual associator. -/
noncomputable def ihomTensorIso (X Y : C) : ihom (X ⊗ Y) ≅ ihom X ⋙ ihom Y :=
  conjugateIsoEquiv (ihom.adjunction (X ⊗ Y))
    ((ihom.adjunction Y).comp (ihom.adjunction X)) (tensorLeftTensor X Y).symm

variable [BraidedCategory C]

/-- The actual right-tensor adjunction, retaining the chosen internal Hom. -/
noncomputable def rightIhomAdjunction (X : C) : tensorRight X ⊣ ihom X :=
  (ihom.adjunction X).ofNatIsoLeft (BraidedCategory.tensorLeftIsoTensorRight X)

/-- The mate of the actual right associator under the chosen right adjunctions. -/
noncomputable def rightIhomTensorIso (X Y : C) : ihom (X ⊗ Y) ≅ ihom Y ⋙ ihom X :=
  conjugateIsoEquiv (rightIhomAdjunction (X ⊗ Y))
    ((rightIhomAdjunction X).comp (rightIhomAdjunction Y)) (tensorRightTensor X Y).symm

end KIP126.StableHomotopy.TensorShift
