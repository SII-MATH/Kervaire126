module

public import KIP126.Def.CategoryTheory.Shift.Integer.Chain.Proofs

@[expose] public section

namespace KIP126.Foundation.IntegerChain

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C] {F : C ⥤ C}

/-- Transport a component backwards along an equality of its index. -/
def transportHom (X Y : IntegerChain F) {m n : ℤ} (h : m = n)
    (f : X.obj n ⟶ Y.obj n) : X.obj m ⟶ Y.obj m :=
  eqToHom (congrArg X.obj h) ≫ f ≫ eqToHom (congrArg Y.obj h.symm)

/-- Extend one component across a forward chain step. -/
def forward (X Y : IntegerChain F) (n : ℤ) (f : X.obj n ⟶ Y.obj n) :
    X.obj (n + 1) ⟶ Y.obj (n + 1) :=
  (X.step n).inv ≫ F.map f ≫ (Y.step n).hom

/-- Extend one component across a backward chain step using actual fullness. -/
noncomputable def backward [F.Full] (X Y : IntegerChain F) (n : ℤ)
    (f : X.obj (n + 1) ⟶ Y.obj (n + 1)) : X.obj n ⟶ Y.obj n :=
  F.preimage ((X.step n).hom ≫ f ≫ (Y.step n).inv)

/-- The entire component family obtained from a map in degree zero. -/
noncomputable def extendFamily [F.Full] (X Y : IntegerChain F)
    (f : X.obj 0 ⟶ Y.obj 0) (n : ℤ) : X.obj n ⟶ Y.obj n :=
  Int.inductionOn' n 0 f (fun k _ g => forward X Y k g)
    (fun k _ g => backward X Y (k - 1) (transportHom X Y (sub_add_cancel k 1) g))

end KIP126.Foundation.IntegerChain
