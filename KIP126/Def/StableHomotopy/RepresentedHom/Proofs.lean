import KIP126.Def.StableHomotopy.RepresentedHom.Data

/-!
# Exactness of represented shifted morphism groups

The three exactness statements use the specified connecting map and hold for
every representing object `P`.  They follow from the actual distinguished
triangle and its shift equivalences; they are not additional exact-couple data.
-/

namespace KIP126.StableHomotopy.RepresentedHom

open CategoryTheory CategoryTheory.Limits Pretriangulated

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]

@[simp] theorem postcomposeHom_apply
    (P : C) (n : ℤ) {X Y : C} (f : X ⟶ Y) (x : ShiftedHom P n X) :
    postcomposeHom P n f x = x ≫ f := rfl

@[simp] theorem postcomposeLinearMap_apply
    (P : C) (n : ℤ) {X Y : C} (f : X ⟶ Y) (x : ShiftedHom P n X) :
    postcomposeLinearMap P n f x = x ≫ f := rfl

@[simp] theorem connectingLinearMap_apply
    (P : C) (T : HoCofiberSequence (C := C)) (n : ℤ) (z : ShiftedHom P n T.Z) :
    connectingLinearMap P T n z = connectingHom P T n z := rfl

private theorem shiftFunctor_map_eq_zero {X Y : C} {f : X ⟶ Y} {n : ℤ}
    (h : (shiftFunctor C n).map f = 0) : f = 0 := by
  have inj := (shiftEquiv C n).functor.map_injective (X := X) (Y := Y)
  apply inj
  change (shiftFunctor C n).map f = (shiftFunctor C n).map 0
  rw [h, (shiftFunctor C n).map_zero]

private theorem comp_h_zero_of_connectingHom_zero
    (P : C) (T : HoCofiberSequence (C := C)) (n : ℤ) (z : ShiftedHom P n T.Z)
    (hz : connectingHom P T n z = 0) : z ≫ T.h = 0 := by
  simp only [connectingHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at hz
  let a :=
    (shiftFunctorAdd' C n (-1) (n - 1) (by omega)).hom.app P ≫
      eqToHom (show (shiftFunctor C n ⋙ shiftFunctor C (-1)).obj P =
        (shiftFunctor C (-1)).obj ((shiftFunctor C n).obj P) by
          simp only [Functor.comp_obj])
  let m := (shiftFunctor C (-1)).map (z ≫ T.h)
  let b :=
    eqToHom (show (shiftFunctor C (-1)).obj ((shiftFunctor C (1 : ℤ)).obj T.X) =
      (shiftFunctor C (1 : ℤ) ⋙ shiftFunctor C (-1)).obj T.X by
        simp only [Functor.comp_obj]) ≫
      (shiftFunctorCompIsoId C 1 (-1) (by omega)).hom.app T.X ≫
        eqToHom (Functor.id_obj T.X)
  have hz' : a ≫ m ≫ b = 0 := by
    simpa [a, m, b] using hz
  have hm' : a ≫ m = 0 := by
    apply (cancel_mono b).1
    simpa [Category.assoc] using hz'
  have hm : m = 0 := by
    apply (cancel_epi a).1
    simpa using hm'
  exact shiftFunctor_map_eq_zero hm

/-- Exactness at the middle vertex: a morphism killed by `g` factors through
the actual first arrow `f` of the distinguished triangle. -/
theorem exact_f (P : C) (T : HoCofiberSequence (C := C)) (n : ℤ) :
    ∀ y : ShiftedHom P n T.Y,
      postcomposeLinearMap P n T.g y = 0 ↔
        ∃ x : ShiftedHom P n T.X, postcomposeLinearMap P n T.f x = y := by
  intro y
  simp only [postcomposeLinearMap_apply]
  constructor
  · intro hy
    obtain ⟨x, hx⟩ := Triangle.coyoneda_exact₂ _ T.distinguished y hy
    exact ⟨x, hx.symm⟩
  · rintro ⟨x, rfl⟩
    have hfg : T.f ≫ T.g = 0 := comp_distTriang_mor_zero₁₂ _ T.distinguished
    simp [Category.assoc, hfg]

/-- Exactness at the cofiber vertex: the kernel of the specified connecting
map is the image of postcomposition with the actual second arrow `g`. -/
theorem exact_g (P : C) (T : HoCofiberSequence (C := C)) (n : ℤ) :
    ∀ z : ShiftedHom P n T.Z,
      connectingLinearMap P T n z = 0 ↔
        ∃ y : ShiftedHom P n T.Y, postcomposeLinearMap P n T.g y = z := by
  intro z
  simp only [connectingLinearMap_apply, postcomposeLinearMap_apply]
  constructor
  · intro hz
    have hz' : z ≫ T.h = 0 := comp_h_zero_of_connectingHom_zero P T n z hz
    obtain ⟨y, hy⟩ := Triangle.coyoneda_exact₃ _ T.distinguished z hz'
    exact ⟨y, hy.symm⟩
  · rintro ⟨y, rfl⟩
    have hgh : T.g ≫ T.h = 0 := comp_distTriang_mor_zero₂₃ _ T.distinguished
    simp only [connectingHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      Category.assoc, hgh,
      Limits.comp_zero, Functor.map_zero, Limits.zero_comp]

/-- Exactness at the shifted first vertex, using the same specified
connecting map and postcomposition with `f` in degree `n - 1`. -/
theorem exact_h (P : C) (T : HoCofiberSequence (C := C)) (n : ℤ) :
    ∀ x : ShiftedHom P (n - 1) T.X,
      postcomposeLinearMap P (n - 1) T.f x = 0 ↔
        ∃ z : ShiftedHom P n T.Z, connectingLinearMap P T n z = x := by
  intro x
  let F := shiftFunctor C (-1 : ℤ)
  let a : (shiftFunctor C (n - 1)).obj P ≅
      F.obj ((shiftFunctor C n).obj P) :=
    (shiftFunctorAdd' C n (-1) (n - 1) (by omega)).app P
  let b := shiftFunctorCompIsoId C (1 : ℤ) (-1) (by omega)
  let bX : F.obj ((shiftFunctor C (1 : ℤ)).obj T.X) ≅ T.X := b.app T.X
  let bY : F.obj ((shiftFunctor C (1 : ℤ)).obj T.Y) ≅ T.Y := b.app T.Y
  have hc (z : ShiftedHom P n T.Z) :
      connectingLinearMap P T n z = a.hom ≫ F.map (z ≫ T.h) ≫ bX.hom := by
    change a.hom ≫ 𝟙 _ ≫ F.map (z ≫ T.h) ≫ 𝟙 _ ≫ bX.hom ≫ 𝟙 _ = _
    simp only [Category.id_comp, Category.comp_id]
  have hb : bX.inv ≫ F.map ((shiftFunctor C (1 : ℤ)).map T.f) =
      T.f ≫ bY.inv := (b.inv.naturality T.f).symm
  constructor
  · intro hx
    change x ≫ T.f = 0 at hx
    let w := F.preimage (a.inv ≫ x ≫ bX.inv)
    have hw : F.map w = a.inv ≫ x ≫ bX.inv := F.map_preimage _
    have hwf : w ≫ (shiftFunctor C (1 : ℤ)).map T.f = 0 := by
      apply F.map_injective
      rw [Functor.map_comp, hw, Functor.map_zero]
      simp only [Category.assoc, hb, ← Category.assoc x T.f, hx,
        Limits.zero_comp, Limits.comp_zero]
    obtain ⟨z, hz⟩ := Triangle.coyoneda_exact₁ _ T.distinguished w hwf
    change ShiftedHom P n T.Z at z
    change w = z ≫ T.h at hz
    refine ⟨z, ?_⟩
    rw [hc, ← hz, hw]
    simp
  · rintro ⟨z, rfl⟩
    change connectingLinearMap P T n z ≫ T.f = 0
    rw [hc]
    have hb' : bX.hom ≫ T.f =
        F.map ((shiftFunctor C (1 : ℤ)).map T.f) ≫ bY.hom :=
      (b.hom.naturality T.f).symm
    have hhf : T.h ≫ (shiftFunctor C (1 : ℤ)).map T.f = 0 :=
      comp_distTriang_mor_zero₃₁ _ T.distinguished
    simp only [Category.assoc, hb', ← F.map_comp_assoc,
      hhf, Limits.comp_zero,
      F.map_zero, Limits.zero_comp]

end KIP126.StableHomotopy.RepresentedHom
