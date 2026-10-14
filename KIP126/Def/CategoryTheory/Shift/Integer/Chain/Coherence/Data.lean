module

public import KIP126.Def.CategoryTheory.Shift.Integer.Chain.Translation.Proofs

@[expose] public section

namespace KIP126.Foundation.IntegerChain

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C]

/-- Integer translation on actual chains, with all addition coherence proved. -/
noncomputable instance hasShift (F : C ⥤ C) : HasShift (IntegerChain F) ℤ :=
  hasShiftMk _ _ {
    F := translate F
    zero := translateZeroIso F
    add := translateAddIso F
    assoc_hom_app := translate_assoc_hom_app F
    zero_add_hom_app := translate_zero_add_hom_app F
    add_zero_hom_app := translate_add_zero_hom_app F }

end KIP126.Foundation.IntegerChain
