module

public import KIP126.Def.CategoryTheory.Shift.Integer.Chain.Data
public import Mathlib.CategoryTheory.EqToHom

@[expose] public section

namespace KIP126.Foundation.IntegerChain

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C] {F : C ⥤ C}

@[simp] theorem id_app (X : IntegerChain F) (n : ℤ) : (𝟙 X : X ⟶ X).app n = 𝟙 _ := rfl

@[simp] theorem comp_app {X Y Z : IntegerChain F} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℤ) :
    (f ≫ g).app n = f.app n ≫ g.app n := rfl

theorem hom_ext {X Y : IntegerChain F} (f g : X ⟶ Y) (h : ∀ n, f.app n = g.app n) :
    f = g := Hom.ext (funext h)

/-- Transport in the integer index is natural in an actual chain map. -/
theorem Hom.app_eqToHom {X Y : IntegerChain F} (f : X ⟶ Y) {m n : ℤ} (h : m = n) :
    f.app m ≫ eqToHom (congrArg Y.obj h) = eqToHom (congrArg X.obj h) ≫ f.app n := by
  subst n
  simp

/-- A componentwise isomorphism satisfying the step square is an isomorphism
of actual integer chains. -/
def isoMk {X Y : IntegerChain F} (e : ∀ n, X.obj n ≅ Y.obj n)
    (h : ∀ n, F.map (e n).hom ≫ (Y.step n).hom = (X.step n).hom ≫ (e (n + 1)).hom) :
    X ≅ Y where
  hom := ⟨fun n => (e n).hom, h⟩
  inv := ⟨fun n => (e n).inv, by
    intro n
    apply (cancel_epi (F.map (e n).hom)).mp
    simp only [← Functor.map_comp_assoc, Iso.hom_inv_id, Functor.map_id, Category.id_comp]
    rw [← Category.assoc, h, Category.assoc, Iso.hom_inv_id, Category.comp_id]⟩
  hom_inv_id := hom_ext _ _ (fun n => (e n).hom_inv_id)
  inv_hom_id := hom_ext _ _ (fun n => (e n).inv_hom_id)

/-- The step of a chain is compatible with equality of integer indices. -/
theorem step_eqToHom (X : IntegerChain F) {m n : ℤ} (h : m = n) :
    F.map (eqToHom (congrArg X.obj h)) ≫ (X.step n).hom =
      (X.step m).hom ≫ eqToHom (congrArg X.obj (congrArg (· + 1) h)) := by
  subst n
  simp

@[simp] theorem eqToHom_app {X Y : IntegerChain F} (h : X = Y) (n : ℤ) :
    (eqToHom h).app n = eqToHom (congrArg (fun Z => Z.obj n) h) := by
  subst Y
  rfl

end KIP126.Foundation.IntegerChain
