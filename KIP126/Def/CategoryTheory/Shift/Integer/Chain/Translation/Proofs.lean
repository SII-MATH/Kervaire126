module

public import KIP126.Def.CategoryTheory.Shift.Integer.Chain.Translation.Data

@[expose] public section

namespace KIP126.Foundation.IntegerChain

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C] (F : C ⥤ C)

theorem translate_assoc_hom_app (a b c : ℤ) (X : IntegerChain F) :
    (translateAddIso F (a + b) c).hom.app X ≫
        (translate F c).map ((translateAddIso F a b).hom.app X) =
      eqToHom (by rw [add_assoc]) ≫ (translateAddIso F a (b + c)).hom.app X ≫
        (translateAddIso F b c).hom.app ((translate F a).obj X) := by
  apply hom_ext
  intro n
  simp only [comp_app, eqToHom_app]
  change eqToHom (congrArg X.obj (add_assoc (a + b) c n)) ≫
      eqToHom (congrArg X.obj (add_assoc a b (c + n))) =
    eqToHom (congrArg X.obj (by omega : (a + b + c) + n = (a + (b + c)) + n)) ≫
      eqToHom (congrArg X.obj (add_assoc a (b + c) n)) ≫
        eqToHom (congrArg X.obj (by omega : a + ((b + c) + n) = a + (b + (c + n))))
  simp only [eqToHom_trans]

theorem translate_zero_add_hom_app (n : ℤ) (X : IntegerChain F) :
    (translateAddIso F 0 n).hom.app X =
      eqToHom (by dsimp [translate]; rw [zero_add]) ≫
        (translate F n).map ((translateZeroIso F).inv.app X) := by
  apply hom_ext
  intro k
  simp only [comp_app, eqToHom_app]
  change eqToHom (congrArg X.obj (add_assoc 0 n k)) =
    eqToHom (congrArg X.obj (by omega : (0 + n) + k = n + k)) ≫
      eqToHom (congrArg X.obj (zero_add (n + k)).symm)
  simp only [eqToHom_trans]

theorem translate_add_zero_hom_app (n : ℤ) (X : IntegerChain F) :
    (translateAddIso F n 0).hom.app X =
      eqToHom (by dsimp [translate]; rw [add_zero]) ≫
        (translateZeroIso F).inv.app ((translate F n).obj X) := by
  apply hom_ext
  intro k
  simp only [comp_app, eqToHom_app]
  change eqToHom (congrArg X.obj (add_assoc n 0 k)) =
    eqToHom (congrArg X.obj (by omega : (n + 0) + k = n + k)) ≫
      eqToHom (congrArg X.obj (by omega : n + k = n + (0 + k)))
  simp only [eqToHom_trans]

end KIP126.Foundation.IntegerChain
