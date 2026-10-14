module

public import KIP126.Def.CategoryTheory.Shift.Integer.Chain.Proofs
public import Mathlib.CategoryTheory.Shift.Basic

@[expose] public section

namespace KIP126.Foundation.IntegerChain

open CategoryTheory

set_option backward.isDefEq.respectTransparency false

universe u v

variable {C : Type u} [Category.{v} C] {F : C ⥤ C}

/-- Translation of an actual chain, with its step transported along integer addition. -/
def translateObj (d : ℤ) (X : IntegerChain F) : IntegerChain F where
  obj n := X.obj (d + n)
  step n := X.step (d + n) ≪≫ eqToIso (congrArg X.obj (add_assoc d n 1))

/-- Translation acts on actual chain maps componentwise. -/
def translate (F : C ⥤ C) (d : ℤ) : IntegerChain F ⥤ IntegerChain F where
  obj := translateObj d
  map f := ⟨fun n => f.app (d + n), by
    intro n
    dsimp [translateObj]
    simp only [Iso.trans_hom, eqToIso.hom]
    rw [← Category.assoc, f.comm, Category.assoc, f.app_eqToHom (add_assoc d n 1),
      ← Category.assoc]⟩

/-- Translation by zero identifies with the original chain. -/
def translateZeroIso (F : C ⥤ C) : translate F 0 ≅ 𝟭 _ :=
  NatIso.ofComponents (fun X => isoMk (fun n => eqToIso (congrArg X.obj (zero_add n)))
    (by
      intro n
      dsimp [Functor.comp_obj, translate, translateObj]
      simp only [Iso.trans_hom, eqToIso.hom]
      simpa only [Iso.trans_hom, eqToIso.hom, Category.assoc, eqToHom_trans] using
        step_eqToHom X (zero_add n))) (by
    intro X Y f
    apply hom_ext
    intro n
    exact f.app_eqToHom (zero_add n))

/-- Addition of translations is induced by associativity of integer addition. -/
def translateAddIso (F : C ⥤ C) (a b : ℤ) :
    translate F (a + b) ≅ translate F a ⋙ translate F b :=
  NatIso.ofComponents (fun X => isoMk
    (fun n => eqToIso (congrArg X.obj (add_assoc a b n))) (by
      intro n
      change F.map (eqToHom (congrArg X.obj (add_assoc a b n))) ≫
          ((translateObj b (translateObj a X)).step n).hom =
        ((translateObj (a + b) X).step n).hom ≫
          eqToHom (congrArg X.obj (add_assoc a b (n + 1)))
      dsimp only [translateObj]
      simp only [Iso.trans_hom, eqToIso.hom, Category.assoc, eqToHom_trans]
      rw [← Category.assoc, step_eqToHom X (add_assoc a b n), Category.assoc, eqToHom_trans])) (by
    intro X Y f
    apply hom_ext
    intro n
    exact f.app_eqToHom (add_assoc a b n))

end KIP126.Foundation.IntegerChain
