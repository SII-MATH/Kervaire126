module

public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.CategoryTheory.Shift.Adjunction

@[expose] public section


/-! The full chosen shift structure of a left adjoint is determined by the
right adjoint's chosen structure and compatibility of their actual unit. -/
namespace KIP126.StableHomotopy.TensorShift
noncomputable section
open CategoryTheory
universe u₁ u₂ v₁ v₂ w
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

private theorem commShift_ext {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D] (F : C ⥤ D) (A : Type w)
    [AddMonoid A] [HasShift C A] [HasShift D A]
    (s t : F.CommShift A) (h : ∀ a, s.commShiftIso a = t.commShiftIso a) : s = t := by
  have he : s.commShiftIso = t.commShiftIso := funext h
  cases s
  cases t
  cases he
  rfl

/-- With the same right adjoint and its same selected shifts, compatibility
with the actual adjunction unit uniquely determines the entire left shift
structure, for every integer shift. -/
theorem leftShift_eq_adjoint {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D] [HasShift C ℤ] [HasShift D ℤ]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    [s : F.CommShift ℤ] [G.CommShift ℤ]
    [NatTrans.CommShift adj.unit ℤ] : s = adj.leftAdjointCommShift ℤ := by
  apply commShift_ext
  intro a
  refine Adjunction.CommShift.compatibilityUnit_unique_left adj _ _ (G.commShiftIso a)
    ?_ (Adjunction.LeftAdjointCommShift.compatibilityUnit_iso adj a)
  intro X
  simpa only [Functor.commShiftIso_id_hom_app, Functor.comp_obj, Functor.id_obj,
    Category.id_comp, Functor.commShiftIso_comp_hom_app, Category.assoc] using!
      (NatTrans.shift_app_comm adj.unit a X)

/-- Transport along the inverse functor isomorphism and then the original
isomorphism recovers the whole chosen shift structure. -/
theorem commShift_ofIso_roundtrip {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D] [HasShift C ℤ] [HasShift D ℤ]
    {F G : C ⥤ D} (e : F ≅ G) [s : G.CommShift ℤ] :
    (letI := Functor.CommShift.ofIso e.symm ℤ
     Functor.CommShift.ofIso e ℤ) = s := by
  apply commShift_ext
  intro a
  apply Iso.ext
  ext X
  simp only [Functor.CommShift.ofIso_commShiftIso_hom_app, Iso.symm_inv,
    Iso.symm_hom, Category.assoc, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp, Iso.inv_hom_id_app]
  rw [(shiftFunctor D a).map_id, Category.comp_id]

section Mates
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [HasShift C ℤ] [HasShift D ℤ]
  {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
  [L₁.CommShift ℤ] [R₁.CommShift ℤ] [L₂.CommShift ℤ] [R₂.CommShift ℤ]
  [adj₁.CommShift ℤ] [adj₂.CommShift ℤ]

/-- Mates preserve the compatibility of the same chosen integer shifts. -/
theorem conjugate_commShift (α : L₂ ⟶ L₁) [NatTrans.CommShift α ℤ] :
    NatTrans.CommShift (conjugateEquiv adj₁ adj₂ α) ℤ := by
  have h : conjugateEquiv adj₁ adj₂ α =
      R₁.rightUnitor.inv ≫ Functor.whiskerLeft R₁ adj₂.unit ≫
      (Functor.associator R₁ L₂ R₂).inv ≫
      Functor.whiskerRight (Functor.whiskerLeft R₁ α) R₂ ≫
      Functor.whiskerRight adj₁.counit R₂ ≫ R₂.leftUnitor.hom := by
    ext X
    simp
  rw [h]
  infer_instance

/-- The reverse mates correspondence also preserves the same shifts. -/
theorem conjugate_symm_commShift (β : R₁ ⟶ R₂) [NatTrans.CommShift β ℤ] :
    NatTrans.CommShift ((conjugateEquiv adj₁ adj₂).symm β) ℤ := by
  have h : (conjugateEquiv adj₁ adj₂).symm β =
      L₂.leftUnitor.inv ≫ Functor.whiskerRight adj₁.unit L₂ ≫
      Functor.whiskerRight (Functor.whiskerLeft L₁ β) L₂ ≫
      (Functor.associator L₁ R₂ L₂).hom ≫
      Functor.whiskerLeft L₁ adj₂.counit ≫ L₁.rightUnitor.hom := by
    ext X
    simp
  rw [h]
  infer_instance

/-- Full integer compatibility is equivalent on the two sides of adjunction. -/
theorem conjugate_commShift_iff (α : L₂ ⟶ L₁) :
    NatTrans.CommShift (conjugateEquiv adj₁ adj₂ α) ℤ ↔ NatTrans.CommShift α ℤ := by
  constructor
  · intro h
    letI := h
    have hh := conjugate_symm_commShift adj₁ adj₂ (conjugateEquiv adj₁ adj₂ α)
    simpa only [Equiv.symm_apply_apply] using hh
  · intro h
    letI := h
    exact conjugate_commShift adj₁ adj₂ α

end Mates

end
end KIP126.StableHomotopy.TensorShift
