module

public import KIP126.Def.CategoryTheory.Shift.Integer.Chain.Evaluation.Data

@[expose] public section

namespace KIP126.Foundation.IntegerChain

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C] {F : C ⥤ C}

@[simp] theorem transportHom_family (X Y : IntegerChain F)
    (f : ∀ n, X.obj n ⟶ Y.obj n) {m n : ℤ} (h : m = n) :
    transportHom X Y h (f n) = f m := by
  subst n
  simp [transportHom]

theorem forward_comm (X Y : IntegerChain F) (n : ℤ) (f : X.obj n ⟶ Y.obj n) :
    F.map f ≫ (Y.step n).hom = (X.step n).hom ≫ forward X Y n f := by
  simp [forward]

theorem backward_comm [F.Full] (X Y : IntegerChain F) (n : ℤ)
    (f : X.obj (n + 1) ⟶ Y.obj (n + 1)) :
    F.map (backward X Y n f) ≫ (Y.step n).hom = (X.step n).hom ≫ f := by
  simp [backward]

@[simp] theorem extendFamily_zero [F.Full] (X Y : IntegerChain F)
    (f : X.obj 0 ⟶ Y.obj 0) : extendFamily X Y f 0 = f :=
  Int.inductionOn'_self

theorem extendFamily_succ [F.Full] (X Y : IntegerChain F)
    (f : X.obj 0 ⟶ Y.obj 0) (n : ℤ) (hn : 0 ≤ n) :
    extendFamily X Y f (n + 1) = forward X Y n (extendFamily X Y f n) :=
  Int.inductionOn'_add_one hn

theorem extendFamily_pred [F.Full] (X Y : IntegerChain F)
    (f : X.obj 0 ⟶ Y.obj 0) (n : ℤ) (hn : n ≤ 0) :
    extendFamily X Y f (n - 1) = backward X Y (n - 1)
      (transportHom X Y (sub_add_cancel n 1) (extendFamily X Y f n)) :=
  Int.inductionOn'_sub_one hn

theorem extendFamily_comm [F.Full] (X Y : IntegerChain F)
    (f : X.obj 0 ⟶ Y.obj 0) (n : ℤ) :
    F.map (extendFamily X Y f n) ≫ (Y.step n).hom =
      (X.step n).hom ≫ extendFamily X Y f (n + 1) := by
  by_cases hn : 0 ≤ n
  · rw [extendFamily_succ X Y f n hn]
    exact forward_comm X Y n _
  · obtain ⟨k, rfl⟩ : ∃ k : ℤ, n = k - 1 := ⟨n + 1, by omega⟩
    rw [extendFamily_pred X Y f k (by omega), backward_comm, transportHom_family]

theorem app_eq_iff_succ [F.Faithful] {X Y : IntegerChain F} (f g : X ⟶ Y) (n : ℤ) :
    f.app n = g.app n ↔ f.app (n + 1) = g.app (n + 1) := by
  constructor
  · intro h
    apply (cancel_epi (X.step n).hom).mp
    rw [← f.comm, ← g.comm, h]
  · intro h
    apply F.map_injective
    apply (cancel_mono (Y.step n).hom).mp
    rw [f.comm, g.comm, h]

theorem hom_ext_zero [F.Faithful] {X Y : IntegerChain F} (f g : X ⟶ Y)
    (h : f.app 0 = g.app 0) : f = g := by
  apply hom_ext
  intro n
  induction n using (Int.inductionOn' · 0) with
  | zero => exact h
  | succ k _ ih => exact (app_eq_iff_succ f g k).mp ih
  | pred k _ ih => exact (app_eq_iff_succ f g (k - 1)).mpr (by
      rw [show k - 1 + 1 = k by omega]
      exact ih)

instance eval_zero_faithful [F.Faithful] : (eval F 0).Faithful where
  map_injective := hom_ext_zero _ _

instance eval_zero_full [F.Full] : (eval F 0).Full where
  map_surjective f := ⟨⟨extendFamily _ _ f, extendFamily_comm _ _ f⟩, extendFamily_zero _ _ f⟩

end KIP126.Foundation.IntegerChain
