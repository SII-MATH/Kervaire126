module

public import KIP126.Def.StableHomotopy.Cohomology.Multiplication.Proofs
public import KIP126.Def.ClassicalAdams.TowerNaturality.Unit.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Cohomology
open CategoryTheory MonoidalCategory KIP126.Classical.Adams
set_option backward.isDefEq.respectTransparency false
universe u v
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)

include R in
/-- An equivalence after coefficient smash is detected by maps into the
same coefficient object. The extension uses its actual multiplication and
unit; no cohomology comparison or conservativity premise is required. -/
theorem precomp_hf2_bijective_of_tensor_isIso {X Y : C} (f : X ⟶ Y)
    [IsIso (H.HF2 ◁ f)] : Function.Bijective (fun a : Y ⟶ H.HF2 => f ≫ a) := by
  have hsplit {Z : C} (a : Z ⟶ H.HF2) :
      adamsUnit H.unit Z ≫ H.HF2 ◁ a ≫ R.monoid.mul = a := by
    rw [← Category.assoc, ← adamsUnit_naturality, Category.assoc, adamsUnit_mul, Category.comp_id]
  constructor
  · intro a b h
    change f ≫ a = f ≫ b at h
    have hh : H.HF2 ◁ a = H.HF2 ◁ b := by
      apply (cancel_epi (H.HF2 ◁ f)).mp
      rw [← whiskerLeft_comp, ← whiskerLeft_comp, h]
    rw [← hsplit a, ← hsplit b, hh]
  · intro a
    refine ⟨adamsUnit H.unit Y ≫ inv (H.HF2 ◁ f) ≫ H.HF2 ◁ a ≫ R.monoid.mul, ?_⟩
    change f ≫ (adamsUnit H.unit Y ≫ inv (H.HF2 ◁ f) ≫ H.HF2 ◁ a ≫ R.monoid.mul) = a
    rw [← Category.assoc, adamsUnit_naturality, Category.assoc, IsIso.hom_inv_id_assoc]
    exact hsplit a

variable [(tensorLeft H.HF2).CommShift ℤ]

include R in
/-- Coefficient-smash equivalences induce bijections on maps into every
integer shift of the coefficient object. Shift compatibility transports
the unshifted splitting argument. -/
theorem precomp_hf2_shift_bijective_of_tensor_isIso {X Y : C} (f : X ⟶ Y)
    [IsIso (H.HF2 ◁ f)] (d : ℤ) :
    Function.Bijective (fun a : Y ⟶ H.HF2⟦d⟧ => f ≫ a) := by
  letI : IsIso ((tensorLeft H.HF2).map f) := ‹IsIso (H.HF2 ◁ f)›
  letI : IsIso (H.HF2 ◁ f⟦-d⟧') := by
    have hn := (tensorLeft H.HF2).commShiftIso_hom_naturality f (-d)
    exact IsIso.of_isIso_fac_right hn
  let e (Z : C) : (Z⟦-d⟧ ⟶ H.HF2) ≃ (Z ⟶ H.HF2⟦d⟧) :=
    (shiftEquiv C d).fullyFaithfulFunctor.homEquiv.trans
      (Iso.homCongr (shiftNegShift Z d) (Iso.refl _))
  have he (a : Y⟦-d⟧ ⟶ H.HF2) : e X (f⟦-d⟧' ≫ a) = f ≫ e Y a := by
    change (shiftNegShift X d).inv ≫ (f⟦-d⟧' ≫ a)⟦d⟧' ≫ 𝟙 _ =
      f ≫ (shiftNegShift Y d).inv ≫ a⟦d⟧' ≫ 𝟙 _
    simp only [Category.comp_id, Functor.map_comp]
    exact ((shiftEquiv C d).counitIso.inv.naturality_assoc f (a⟦d⟧')).symm
  have h := precomp_hf2_bijective_of_tensor_isIso H R (f⟦-d⟧')
  constructor
  · intro a b hab
    obtain ⟨a, rfl⟩ := (e Y).surjective a
    obtain ⟨b, rfl⟩ := (e Y).surjective b
    apply congrArg (e Y)
    apply h.injective
    apply (e X).injective
    rw [he a, he b]
    exact hab
  · intro a
    obtain ⟨a, rfl⟩ := (e X).surjective a
    obtain ⟨b, hb⟩ := h.surjective a
    refine ⟨e Y b, ?_⟩
    change f ≫ e Y b = e X a
    change f⟦-d⟧' ≫ b = a at hb
    rw [← he b, hb]

end KIP126.StableHomotopy.Cohomology
