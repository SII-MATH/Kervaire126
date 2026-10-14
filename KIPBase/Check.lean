import KIPBase.Mathlib
open CategoryTheory CategoryTheory.Limits
-- Unavailable in pinned Mathlib: #check AddCommGrpCat.isZero_iff
-- Unavailable in pinned Mathlib: #check AddCommGrpCat.isZero_iff_subsingleton
-- Unavailable in pinned Mathlib: #check AddCommGrpCat.subsingleton_of_isZero
-- Unavailable in pinned Mathlib: #check isZero_iff_subsingleton
#check IsZero.of_iso
#check AddEquiv.toIntLinearEquiv
#check AddEquiv.toAddMonoidHom
-- Unavailable in pinned Mathlib: #check AddEquiv.ofEq
-- Unavailable in pinned Mathlib: #check Equiv.toAddEquiv
-- Unavailable in pinned Mathlib: #check AddCommGrpCat.isZero_of_subsingleton
-- Unavailable in pinned Mathlib: #check isZero_of_subsingleton
-- Unavailable in pinned Mathlib: #check isZero_of_subsingleton_object
#check IsZero.iff_id_eq_zero
-- Unavailable in pinned Mathlib: #check isZero_of_identity_eq_zero
#check AddCommGrpCat.ofHom
#check AddCommGrpCat.hom_ext
#check IsZero.eq_of_src
#check IsZero.eq_of_tgt
-- Unavailable in pinned Mathlib: #check IsZero.eq_of_src_eq_tgt
#check IsZero.isoZero
#check AddCommGrpCat.of

theorem test_subsingleton (A : AddCommGrpCat) (h : IsZero A) :
    Subsingleton A where
  allEq a b := by
    have hi : (𝟙 A : A ⟶ A) = 0 := h.eq_of_src _ _
    calc
      a = (𝟙 A : A ⟶ A) a := rfl
      _ = (0 : A ⟶ A) a := congrArg (fun f : A ⟶ A => f a) hi
      _ = 0 := rfl
      _ = (0 : A ⟶ A) b := rfl
      _ = (𝟙 A : A ⟶ A) b := congrArg (fun f : A ⟶ A => f b) hi.symm
      _ = b := rfl
