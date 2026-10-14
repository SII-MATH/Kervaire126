module

public import KIP126.Def.StableHomotopy.Completion.Moore.Torsion.Proofs
public import KIP126.Def.StableHomotopy.Completion.Moore.Orthogonality.Proofs
public import KIP126.Def.StableHomotopy.RepresentedHom.Proofs
public import KIP126.Def.CategoryTheory.Triangulated.Represented.Proofs

@[expose] public section

namespace KIP126.StableHomotopy

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

set_option backward.isDefEq.respectTransparency false

universe u v

section Cofiber

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasFunctorialCofiber (C := C)]

/-- A scalar is invertible if the shifted cofiber of that scalar has no
nonzero morphisms to its original object. -/
theorem isIso_nsmul_id_of_shifted_cofiber_hom_subsingleton (p : ℕ) (Z : C)
    [Subsingleton ((HasFunctorialCofiber.cofib (p • 𝟙 Z))⟦(-1 : ℤ)⟧ ⟶ Z)] :
    IsIso (p • 𝟙 Z) := by
  let f := p • 𝟙 Z
  let T := Triangle.mk f (HasFunctorialCofiber.cofibι f)
    (HasFunctorialCofiber.cofibδ f)
  have hT := HasFunctorialCofiber.cofib_distinguished f
  letI : Subsingleton (T.invRotate.obj₁ ⟶ Z) := inferInstanceAs
    (Subsingleton ((HasFunctorialCofiber.cofib (p • 𝟙 Z))⟦(-1 : ℤ)⟧ ⟶ Z))
  obtain ⟨r, hr⟩ := T.invRotate.yoneda_exact₂ (inv_rot_of_distTriang T hT) (𝟙 Z)
    (Subsingleton.elim _ _)
  change 𝟙 Z = (p • 𝟙 Z) ≫ r at hr
  have hl : r ≫ (p • 𝟙 Z) = 𝟙 Z := by
    simpa only [Preadditive.nsmul_comp, Preadditive.comp_nsmul,
      Category.id_comp, Category.comp_id] using hr.symm
  exact ⟨⟨r, hr.symm, hl⟩⟩

end Cofiber

section Shifted

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]

/-- Surjectivity on represented morphisms and injectivity in the preceding
degree force the represented morphisms to the actual cofiber to vanish. -/
theorem shiftedHom_cofiber_subsingleton_of_postcomp
    {X Y : C} (f : X ⟶ Y) (U : C) (n : ℤ)
    (hs : Function.Surjective (fun a : ShiftedHom U n X => a ≫ f))
    (hi : Function.Injective (fun a : ShiftedHom U (n - 1) X => a ≫ f)) :
    Subsingleton (ShiftedHom U n (HasFunctorialCofiber.cofib f)) := by
  let T := HoCofiberSequence.ofMorphism f
  have hz (z : ShiftedHom U n T.Z) : z = 0 := by
    have hc : connectingLinearMap U T n z = 0 := by
      apply hi
      change connectingLinearMap U T n z ≫ T.f = (0 : ShiftedHom U (n - 1) T.X) ≫ T.f
      rw [zero_comp]
      exact (RepresentedHom.exact_h U T n _).mpr ⟨z, rfl⟩
    obtain ⟨y, hy⟩ := (RepresentedHom.exact_g U T n z).mp hc
    obtain ⟨x, hx⟩ := hs y
    change y ≫ T.g = z at hy
    change x ≫ T.f = y at hx
    rw [← hy, ← hx, Category.assoc, T.fg_zero, comp_zero]
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩

end Shifted

section Cofiber

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasFunctorialCofiber (C := C)]

/-- Testing a map on all objects annihilated by the square of the scalar
detects scalar invertibility on its cofiber. -/
theorem isIso_nsmul_id_cofiber_of_torsion_postcomp_bijective
    (p : ℕ) {X Y : C} (f : X ⟶ Y)
    (hf : ∀ U : C, p ^ 2 • 𝟙 U = 0 →
      Function.Bijective (fun a : U ⟶ X => a ≫ f)) :
    IsIso (p • 𝟙 (HasFunctorialCofiber.cofib f)) := by
  let Z := HasFunctorialCofiber.cofib f
  let U := (HasFunctorialCofiber.cofib (p • 𝟙 Z))⟦(-1 : ℤ)⟧
  have hU : p ^ 2 • 𝟙 U = 0 :=
    nsmul_pow_id_shift_eq_zero p (nsmul_square_id_cofiber_eq_zero p Z) (-1)
  let T := Triangle.mk f (HasFunctorialCofiber.cofibι f)
    (HasFunctorialCofiber.cofibδ f)
  letI : Subsingleton (U ⟶ Z) :=
    KIP126.Foundation.hom_triangle_third_subsingleton_of_postcomp T
      (HasFunctorialCofiber.cofib_distinguished f) U (hf U hU).surjective
      (hf (U⟦(-1 : ℤ)⟧) (nsmul_pow_id_shift_eq_zero p hU (-1))).injective
  exact isIso_nsmul_id_of_shifted_cofiber_hom_subsingleton p Z

/-- Objects orthogonal to scalar-invertible objects have unique extension
along every map with scalar-invertible cofiber. -/
theorem precomp_bijective_of_scalar_cofiber_orthogonal
    (p : ℕ) {X Y : C} (f : X ⟶ Y)
    [IsIso (p • 𝟙 (HasFunctorialCofiber.cofib f))] (L : C)
    (hL : ∀ U : C, IsIso (p • 𝟙 U) → Subsingleton (U ⟶ L)) :
    Function.Bijective (fun a : Y ⟶ L => f ≫ a) := by
  let T := Triangle.mk f (HasFunctorialCofiber.cofibι f)
    (HasFunctorialCofiber.cofibδ f)
  have hT := HasFunctorialCofiber.cofib_distinguished f
  letI : Subsingleton (T.obj₃ ⟶ L) := hL _
    (inferInstanceAs (IsIso (p • 𝟙 (HasFunctorialCofiber.cofib f))))
  letI : Subsingleton (T.invRotate.obj₁ ⟶ L) :=
    hL _ (isIso_nsmul_id_shift p (HasFunctorialCofiber.cofib f) (-1))
  constructor
  · intro a b hab
    apply sub_eq_zero.mp
    have hab' : f ≫ (a - b) = 0 := by
      change f ≫ a = f ≫ b at hab
      rw [Preadditive.comp_sub, hab, sub_self]
    obtain ⟨z, hz⟩ := T.yoneda_exact₂ hT (a - b) hab'
    rw [show z = 0 from Subsingleton.elim _ _] at hz
    simpa only [comp_zero] using hz
  · intro a
    obtain ⟨b, hb⟩ := T.invRotate.yoneda_exact₂ (inv_rot_of_distTriang T hT) a
      (Subsingleton.elim _ _)
    exact ⟨b, hb.symm⟩

end Cofiber

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [HasProductsOfShape ℕ C]

/-- The cofiber of an actual Moore unit has invertible scalar action.
The unit is identified by its prescribed cofiber projections. -/
theorem mooreCompletion_unit_cofiber_scalar_isIso (p : ℕ) (X : C)
    (u : X ⟶ mooreCompletion p X)
    (hu : ∀ k, u ≫ (moorePowerSequence p X).homotopyLimitWitness.π k =
      HasFunctorialCofiber.cofibι (moorePowerMap p X k)) :
    IsIso (p • 𝟙 (HasFunctorialCofiber.cofib u)) := by
  apply isIso_nsmul_id_cofiber_of_torsion_postcomp_bijective p u
  intro U hU
  exact mooreCompletion_unit_postcomp_bijective_of_torsion p X U hU u hu

/-- Every actual Moore unit is universal into all objects orthogonal to
scalar-invertible objects. -/
theorem mooreCompletion_unit_precomp_bijective (p : ℕ) (X : C)
    (u : X ⟶ mooreCompletion p X)
    (hu : ∀ k, u ≫ (moorePowerSequence p X).homotopyLimitWitness.π k =
      HasFunctorialCofiber.cofibι (moorePowerMap p X k))
    (L : C) (hL : ∀ U : C, IsIso (p • 𝟙 U) → Subsingleton (U ⟶ L)) :
    Function.Bijective (fun a : mooreCompletion p X ⟶ L => u ≫ a) := by
  letI := mooreCompletion_unit_cofiber_scalar_isIso p X u hu
  exact precomp_bijective_of_scalar_cofiber_orthogonal p u L hL

/-- The constructed Moore limit admits its prescribed unit, whose cofiber
is scalar-invertible and which is universal into every scalar-complete object,
expressed intrinsically by orthogonality to scalar-invertible objects. -/
theorem mooreCompletion_exists_universal_unit (p : ℕ) (X : C) :
    ∃ u : X ⟶ mooreCompletion p X,
      (∀ k, u ≫ (moorePowerSequence p X).homotopyLimitWitness.π k =
        HasFunctorialCofiber.cofibι (moorePowerMap p X k)) ∧
      IsIso (p • 𝟙 (HasFunctorialCofiber.cofib u)) ∧
      ∀ L : C, (∀ U : C, IsIso (p • 𝟙 U) → Subsingleton (U ⟶ L)) →
        Function.Bijective (fun a : mooreCompletion p X ⟶ L => u ≫ a) := by
  obtain ⟨u, hu⟩ := mooreCompletion_exists_unit p X
  exact ⟨u, hu, mooreCompletion_unit_cofiber_scalar_isIso p X u hu,
    mooreCompletion_unit_precomp_bijective p X u hu⟩

end KIP126.StableHomotopy
