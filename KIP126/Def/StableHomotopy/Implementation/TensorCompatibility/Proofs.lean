module

public import KIP126.Def.StableHomotopy.Context.TensorSuspension.Adjunction.Proofs
public import KIP126.Def.StableHomotopy.Context.TensorSuspension.Closed.Proofs
public import KIP126.Def.StableHomotopy.Context.TensorSuspension.Braiding.Construction.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Data

@[expose] public section


namespace KIP126.Foundation.TensorInput
open KIP126.StableHomotopy

/-- The same foundation's specified left shifts are transported from its
right shifts by braiding. Hence this side of tensor-boundary compatibility
is already supplied, with no new field or ambient structure choice. -/
theorem tensorSuspensionBraidingCompatibility (F : FoundationInput) [TensorInput F] :
    TensorSuspensionBraidingCompatibility (C := F.Spectrum) :=
  tensorSuspensionBraidingCompatibility_of_leftShift_eq (TensorInput.leftShift_eq)

open CategoryTheory MonoidalCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- The existing internal-Hom unit compatibility reconstructs the complete
specified left-tensor shift structure, for all objects and integer shifts. -/
theorem leftShift_eq_adjoint (F : FoundationInput) [T : TensorInput F]
    (X : F.Spectrum) :
    T.leftShift X = (ihom.adjunction X).leftAdjointCommShift ℤ := by
  letI := TensorInput.ihom_unit_shift X
  exact StableHomotopy.TensorShift.leftShift_eq_adjoint (ihom.adjunction X)

/-- Reconstructing through the same internal-Hom shifts and braiding gives
the original entire right-tensor shift structure. This does not supply its
separate right-parameter naturality or associator compatibility. -/
theorem rightShift_eq_adjoint (F : FoundationInput) [T : TensorInput F]
    (X : F.Spectrum) :
    T.rightShift X =
      (letI := (ihom.adjunction X).leftAdjointCommShift ℤ
       Functor.CommShift.ofIso (BraidedCategory.tensorLeftIsoTensorRight X) ℤ) := by
  rw [← leftShift_eq_adjoint F X]
  have hl := TensorInput.leftShift_eq (F := F) X
  rw [hl]
  exact (StableHomotopy.TensorShift.commShift_ofIso_roundtrip
    (BraidedCategory.tensorLeftIsoTensorRight X)).symm

open KIP126.StableHomotopy.TensorShift

section ShiftFamily
variable (F : FoundationInput) [T : TensorInput F]

/-- The original braiding comparison commutes with every integer shift. -/
theorem tensorBraiding_commShift (X : F.Spectrum) :
    NatTrans.CommShift (BraidedCategory.tensorLeftIsoTensorRight X).hom ℤ := by
  rw [Foundation.TensorInput.leftShift_eq (F := F) X]
  letI : (tensorLeft X).CommShift ℤ := Functor.CommShift.ofIso
    (BraidedCategory.tensorLeftIsoTensorRight X).symm ℤ
  letI : NatTrans.CommShift (BraidedCategory.tensorLeftIsoTensorRight X).symm.hom ℤ :=
    Functor.CommShift.ofIso_compatibility (BraidedCategory.tensorLeftIsoTensorRight X).symm ℤ
  exact NatTrans.CommShift.of_iso_inv (BraidedCategory.tensorLeftIsoTensorRight X).symm ℤ

/-- Exact equivalence of the two full integer family comparisons on the original inputs. -/
theorem ihom_pre_commShift_iff {X Y : F.Spectrum} (f : X ⟶ Y) :
    NatTrans.CommShift (MonoidalClosed.pre f) ℤ ↔
      NatTrans.CommShift ((tensoringLeft F.Spectrum).map f) ℤ := by
  letI : (ihom.adjunction X).CommShift ℤ :=
    Adjunction.CommShift.mk' _ _ (Foundation.TensorInput.ihom_unit_shift X)
  letI : (ihom.adjunction Y).CommShift ℤ :=
    Adjunction.CommShift.mk' _ _ (Foundation.TensorInput.ihom_unit_shift Y)
  exact conjugate_commShift_iff (ihom.adjunction Y) (ihom.adjunction X) _

/-- Right- and left-parameter naturality are equivalent for the original shifted tensors. -/
theorem tensor_parameter_commShift_iff {X Y : F.Spectrum} (f : X ⟶ Y) :
    NatTrans.CommShift ((tensoringRight F.Spectrum).map f) ℤ ↔
      NatTrans.CommShift ((tensoringLeft F.Spectrum).map f) ℤ := by
  letI := tensorBraiding_commShift F X
  letI := tensorBraiding_commShift F Y
  have hr : (tensoringRight F.Spectrum).map f =
      (BraidedCategory.tensorLeftIsoTensorRight X).inv ≫
      (tensoringLeft F.Spectrum).map f ≫
      (BraidedCategory.tensorLeftIsoTensorRight Y).hom := by
    ext B
    simp [BraidedCategory.tensorLeftIsoTensorRight, BraidedCategory.braiding_naturality_left]
  have hl : (tensoringLeft F.Spectrum).map f =
      (BraidedCategory.tensorLeftIsoTensorRight X).hom ≫
      (tensoringRight F.Spectrum).map f ≫
      (BraidedCategory.tensorLeftIsoTensorRight Y).inv := by
    rw [hr]
    simp
  constructor
  · intro h
    letI := h
    rw [hl]
    infer_instance
  · intro h
    letI := h
    rw [hr]
    infer_instance

/-- The exact right-parameter target is equivalent to precomposition on the original ihom shifts. -/
theorem ihom_pre_right_commShift_iff {X Y : F.Spectrum} (f : X ⟶ Y) :
    NatTrans.CommShift (MonoidalClosed.pre f) ℤ ↔
      NatTrans.CommShift ((tensoringRight F.Spectrum).map f) ℤ :=
  (ihom_pre_commShift_iff F f).trans (tensor_parameter_commShift_iff F f).symm

/-- Currying with the original ihom shifts is equivalent to the actual inverse associator
commuting with the original left-tensor shifts. Neither side is presumed established. -/
theorem ihom_curry_commShift_iff (X Y : F.Spectrum) :
    NatTrans.CommShift (ihomTensorIso X Y).hom ℤ ↔
      NatTrans.CommShift (tensorLeftTensor X Y).inv ℤ := by
  letI : ∀ Z : F.Spectrum, (ihom.adjunction Z).CommShift ℤ := fun Z ↦
    Adjunction.CommShift.mk' _ _ (Foundation.TensorInput.ihom_unit_shift Z)
  exact conjugate_commShift_iff (ihom.adjunction (X ⊗ Y))
    ((ihom.adjunction Y).comp (ihom.adjunction X)) _

/-- The existing unit and braiding fix compatibility of the right adjunction
with the ORIGINAL shift structures, on all objects and all integers. -/
theorem rightIhomAdjunction_commShift (X : F.Spectrum) :
    (rightIhomAdjunction X).CommShift ℤ := by
  letI := tensorBraiding_commShift F X
  letI := Foundation.TensorInput.ihom_unit_shift X
  apply Adjunction.CommShift.mk'
  change NatTrans.CommShift ((ihom.adjunction X).unit ≫
    Functor.whiskerRight (BraidedCategory.tensorLeftIsoTensorRight X).hom (ihom X)) ℤ
  infer_instance

/-- Full integer right reassociation is equivalent to compatibility of its
actual right-adjoint mate; this does not establish either family condition. -/
theorem rightIhom_curry_commShift_iff (X Y : F.Spectrum) :
    NatTrans.CommShift (rightIhomTensorIso X Y).hom ℤ ↔
      NatTrans.CommShift (tensorRightTensor X Y).inv ℤ := by
  letI : ∀ Z : F.Spectrum, (rightIhomAdjunction Z).CommShift ℤ :=
    rightIhomAdjunction_commShift F
  exact conjugate_commShift_iff (rightIhomAdjunction (X ⊗ Y))
    ((rightIhomAdjunction X).comp (rightIhomAdjunction Y)) _

/-- The entire original right shift is reconstructed by this actual right adjunction. -/
theorem rightShift_eq_rightIhomAdjunction
    (X : F.Spectrum) :
    T.rightShift X = (rightIhomAdjunction X).leftAdjointCommShift ℤ := by
  letI := rightIhomAdjunction_commShift F X
  exact StableHomotopy.TensorShift.leftShift_eq_adjoint (rightIhomAdjunction X)

/-- Right evaluation uses the original all-integer shift comparisons. -/
theorem rightEvaluation_shift (X B : F.Spectrum) (n : ℤ) :
    (((ihom X).commShiftIso n).hom.app B ▷ X) ≫
        ((tensorRight X).commShiftIso n).hom.app ((ihom X).obj B) ≫
        ((β_ X ((ihom X).obj B)).inv ≫ (ihom.ev X).app B)⟦n⟧' =
      (β_ X ((ihom X).obj (B⟦n⟧))).inv ≫ (ihom.ev X).app (B⟦n⟧) := by
  letI := rightIhomAdjunction_commShift F X
  simpa only [Functor.commShiftIso_comp_hom_app, rightIhomAdjunction,
    Adjunction.ofNatIsoLeft, NatTrans.comp_app, Functor.whiskerLeft_app,
    BraidedCategory.tensorLeftIsoTensorRight_inv_app, tensorRight, curriedTensor,
    Functor.flip, Functor.comp_obj, Functor.id_obj, ihom.ev, Category.assoc] using
      (rightIhomAdjunction X).commShiftIso_hom_app_counit_app_shift ℤ n B

/-- Precise remaining all-integer associator comparison on the original family.
The theorem establishes an equivalence, not the condition on either side. -/
theorem right_associator_commShift_iff (X Y : F.Spectrum) :
    NatTrans.CommShift (tensorRightTensor X Y).inv ℤ ↔
      NatTrans.CommShift
        (MonoidalClosed.pre (β_ Y X).hom ≫ (ihomTensorIso Y X).hom) ℤ := by
  rw [← rightIhomTensorIso_hom]
  exact (rightIhom_curry_commShift_iff F X Y).symm

end ShiftFamily

end KIP126.Foundation.TensorInput
