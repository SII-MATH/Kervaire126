module

public import KIP126.Def.StableHomotopy.Completion.Moore.Proofs
public import KIP126.Def.StableHomotopy.InverseSequence.HomotopyLimit.Orthogonality.Proofs

@[expose] public section

namespace KIP126.StableHomotopy

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

set_option backward.isDefEq.respectTransparency false

universe u v

section Scalars

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Invertibility of a scalar on the representing object makes scalar
postcomposition bijective on every represented morphism group. -/
theorem postcomp_nsmul_id_bijective (p : ℕ) (U X : C) [IsIso (p • 𝟙 U)] :
    Function.Bijective (fun a : U ⟶ X => a ≫ (p • 𝟙 X)) := by
  have hc (a : U ⟶ X) : a ≫ (p • 𝟙 X) = (p • 𝟙 U) ≫ a := by
    simp only [Preadditive.comp_nsmul, Preadditive.nsmul_comp,
      Category.comp_id, Category.id_comp]
  constructor
  · intro a b h
    change a ≫ (p • 𝟙 X) = b ≫ (p • 𝟙 X) at h
    rw [hc, hc] at h
    exact (cancel_epi (p • 𝟙 U)).mp h
  · intro a
    refine ⟨inv (p • 𝟙 U) ≫ a, ?_⟩
    change (inv (p • 𝟙 U) ≫ a) ≫ (p • 𝟙 X) = a
    rw [hc]
    simp only [IsIso.hom_inv_id_assoc]

/-- Every natural power of an invertible scalar is invertible. -/
theorem isIso_nsmul_pow_id (p : ℕ) (U : C) [IsIso (p • 𝟙 U)] (k : ℕ) :
    IsIso (p ^ k • 𝟙 U) := by
  induction k with
  | zero => simp only [pow_zero, one_smul]; infer_instance
  | succ k ih =>
    letI := ih
    have h : p ^ (k + 1) • 𝟙 U = (p • 𝟙 U) ≫ (p ^ k • 𝟙 U) := by
      simp only [Preadditive.nsmul_comp, Category.id_comp, smul_smul, pow_succ']
    rw [h]
    infer_instance

/-- Shifts preserve scalar invertibility because they are additive functors. -/
theorem isIso_nsmul_id_shift [HasShift C ℤ]
    [∀ d : ℤ, (shiftFunctor C d).Additive]
    (p : ℕ) (U : C) [IsIso (p • 𝟙 U)] (d : ℤ) :
    IsIso (p • 𝟙 (U⟦d⟧)) := by
  have h : (shiftFunctor C d).map (p • 𝟙 U) = p • 𝟙 (U⟦d⟧) := by
    rw [Functor.map_nsmul, CategoryTheory.Functor.map_id]
  rw [← h]
  infer_instance

end Scalars

variable {C : Type u} [StableHomotopyCategory.{u, v} C]

variable [HasFunctorialCofiber (C := C)]

/-- A scalar cofiber receives only the zero map from an object on which
that scalar is invertible. Exactness uses the actual cofiber triangle. -/
theorem moorePowerSequence_hom_subsingleton (p : ℕ) (X U : C)
    [IsIso (p • 𝟙 U)] (k : ℕ) :
    Subsingleton (U ⟶ (moorePowerSequence p X).obj k) := by
  letI := isIso_nsmul_pow_id p U k
  let T := HoCofiberSequence.ofMorphism (moorePowerMap p X k)
  have hz (z : U ⟶ T.Z) : z = 0 := by
    have hb : z ≫ T.h = 0 := by
      apply (postcomp_nsmul_id_bijective (p ^ k) U (X⟦(1 : ℤ)⟧)).injective
      have hf : (shiftFunctor C (1 : ℤ)).map T.f = p ^ k • 𝟙 (X⟦(1 : ℤ)⟧) := by
        change (shiftFunctor C (1 : ℤ)).map (p ^ k • 𝟙 X) = _
        rw [Functor.map_nsmul, CategoryTheory.Functor.map_id]
      change (z ≫ T.h) ≫ (p ^ k • 𝟙 (X⟦(1 : ℤ)⟧)) = 0 ≫ _
      rw [← hf, Category.assoc, T.hf_shift_zero, comp_zero, zero_comp]
    obtain ⟨y, hy⟩ := Triangle.coyoneda_exact₃ _ T.distinguished z hb
    change z = y ≫ T.g at hy
    obtain ⟨x, hx⟩ := (postcomp_nsmul_id_bijective (p ^ k) U X).surjective y
    change x ≫ T.f = y at hx
    rw [hy, ← hx, Category.assoc, T.fg_zero, comp_zero]
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩

/-- Every shift of a scalar-invertible object is orthogonal to each
actual stage of the Moore tower. -/
theorem moorePowerSequence_shiftedHom_subsingleton (p : ℕ) (X U : C)
    [IsIso (p • 𝟙 U)] (d : ℤ) (k : ℕ) :
    Subsingleton (ShiftedHom U d ((moorePowerSequence p X).obj k)) := by
  letI := isIso_nsmul_id_shift p U d
  exact moorePowerSequence_hom_subsingleton p X (U⟦d⟧) k

variable [HasProductsOfShape ℕ C]

/-- The constructed Moore completion is orthogonal to every integer shift
of every scalar-invertible object. This is proved from its actual tower. -/
theorem mooreCompletion_shiftedHom_subsingleton (p : ℕ) (X U : C)
    [IsIso (p • 𝟙 U)] (d : ℤ) :
    Subsingleton (ShiftedHom U d (mooreCompletion p X)) :=
  (moorePowerSequence p X).homotopyLimitWitness.shiftedHom_subsingleton U d
    (moorePowerSequence_shiftedHom_subsingleton p X U d)
    (moorePowerSequence_shiftedHom_subsingleton p X U (d + 1))

/-- The unshifted orthogonality statement, removing the shift-zero iso. -/
theorem mooreCompletion_hom_subsingleton (p : ℕ) (X U : C)
    [IsIso (p • 𝟙 U)] : Subsingleton (U ⟶ mooreCompletion p X) := by
  letI := mooreCompletion_shiftedHom_subsingleton p X U 0
  have hi : Function.Injective
      (fun a : U ⟶ mooreCompletion p X => (shiftFunctorZero C ℤ).hom.app U ≫ a) :=
    fun _ _ h => (cancel_epi ((shiftFunctorZero C ℤ).hom.app U)).mp h
  exact hi.subsingleton

/-- The constructed completion is local for every map whose actual cofiber
has invertible scalar action. This proves the right lifting property, not
just a vanishing assertion for the individual Moore stages. -/
theorem mooreCompletion_precomp_bijective (p : ℕ) (X : C) {A B : C} (f : A ⟶ B)
    [IsIso (p • 𝟙 (HasFunctorialCofiber.cofib f))] :
    Function.Bijective (fun a : B ⟶ mooreCompletion p X => f ≫ a) := by
  let T := Triangle.mk f (HasFunctorialCofiber.cofibι f) (HasFunctorialCofiber.cofibδ f)
  have hT := HasFunctorialCofiber.cofib_distinguished f
  letI : Subsingleton (T.obj₃ ⟶ mooreCompletion p X) :=
    mooreCompletion_hom_subsingleton p X (HasFunctorialCofiber.cofib f)
  letI : Subsingleton (T.invRotate.obj₁ ⟶ mooreCompletion p X) :=
    mooreCompletion_shiftedHom_subsingleton p X (HasFunctorialCofiber.cofib f) (-1)
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

end KIP126.StableHomotopy
