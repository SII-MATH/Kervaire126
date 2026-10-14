module

public import KIP126.Def.StableHomotopy.Completion.Moore.ScalarInverse.Data
public import KIP126.Def.StableHomotopy.Completion.Moore.Orthogonality.Proofs

@[expose] public section

namespace KIP126.StableHomotopy

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

set_option backward.isDefEq.respectTransparency false

universe u v

section ScalarCofiber

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ d : ℤ, (shiftFunctor C d).Additive] [Pretriangulated C]
  [HasFunctorialCofiber (C := C)]

/-- In the cofiber of `1 - p g`, multiplication by `p` is surjective on
every represented group. Both lifts are constructed by triangle exactness. -/
theorem postcomp_nsmul_id_surjective_cofiber_one_sub_nsmul
    (p : ℕ) {X : C} (g : X ⟶ X) (W : C) :
    Function.Surjective (fun a : W ⟶ HasFunctorialCofiber.cofib (𝟙 X - p • g) =>
      a ≫ (p • 𝟙 _)) := by
  let f := 𝟙 X - p • g
  let Z := HasFunctorialCofiber.cofib f
  let i : X ⟶ Z := HasFunctorialCofiber.cofibι f
  let δ : Z ⟶ X⟦(1 : ℤ)⟧ := HasFunctorialCofiber.cofibδ f
  let T := Triangle.mk f i δ
  have hT := HasFunctorialCofiber.cofib_distinguished f
  let F := shiftFunctor C (1 : ℤ)
  let g' := F.map g
  have hf : F.map f = 𝟙 (F.obj X) - p • g' := by
    simp only [f, Functor.map_sub, Functor.map_nsmul, CategoryTheory.Functor.map_id, g', F]
  have hgf : g' ≫ F.map f = F.map f ≫ g' := by
    rw [hf]
    simp only [Preadditive.comp_sub, Preadditive.sub_comp,
      Preadditive.comp_nsmul, Preadditive.nsmul_comp, Category.comp_id, Category.id_comp]
  have hδ : δ ≫ F.map f = 0 := comp_distTriang_mor_zero₃₁ T hT
  have hι : p • (g ≫ i) = i := by
    have h := comp_distTriang_mor_zero₁₂ T hT
    change (𝟙 X - p • g) ≫ i = 0 at h
    simp only [Preadditive.sub_comp, Preadditive.nsmul_comp, Category.id_comp] at h
    exact (sub_eq_zero.mp h).symm
  intro z
  change W ⟶ Z at z
  have hb : z ≫ δ = p • ((z ≫ δ) ≫ g') := by
    have h : (z ≫ δ) ≫ F.map f = 0 := by
      rw [Category.assoc, hδ, comp_zero]
    rw [hf, Preadditive.comp_sub, Category.comp_id, Preadditive.comp_nsmul] at h
    exact sub_eq_zero.mp h
  have hbg : ((z ≫ δ) ≫ g') ≫ F.map f = 0 := by
    calc
      ((z ≫ δ) ≫ g') ≫ F.map f = (z ≫ δ) ≫ (g' ≫ F.map f) := Category.assoc ..
      _ = (z ≫ δ) ≫ (F.map f ≫ g') := by rw [hgf]
      _ = z ≫ (δ ≫ F.map f) ≫ g' := by simp only [Category.assoc]
      _ = 0 := by rw [hδ, zero_comp, comp_zero]
  obtain ⟨y, hy⟩ := T.coyoneda_exact₁ hT ((z ≫ δ) ≫ g') hbg
  change W ⟶ Z at y
  change (z ≫ δ) ≫ g' = y ≫ δ at hy
  have hdiff : (z - p • y) ≫ δ = 0 := by
    rw [Preadditive.sub_comp, Preadditive.nsmul_comp, ← hy]
    exact sub_eq_zero.mpr hb
  obtain ⟨a, ha⟩ := T.coyoneda_exact₃ hT (z - p • y) hdiff
  change W ⟶ X at a
  change z - p • y = a ≫ i at ha
  have hadj : p • (a ≫ g ≫ i) = a ≫ i := by
    rw [← Preadditive.comp_nsmul, hι]
  refine ⟨y + a ≫ g ≫ i, ?_⟩
  change (y + a ≫ g ≫ i) ≫ (p • 𝟙 Z) = z
  rw [Preadditive.comp_nsmul, Category.comp_id, smul_add, hadj, ← ha]
  abel

/-- Scalar multiplication is invertible on the actual cofiber of `1 - p g`.
Surjectivity on endomorphisms gives an inverse; scalar centrality gives
the second inverse equation. -/
theorem isIso_nsmul_id_cofiber_one_sub_nsmul (p : ℕ) {X : C} (g : X ⟶ X) :
    IsIso (p • 𝟙 (HasFunctorialCofiber.cofib (𝟙 X - p • g))) := by
  let Y := HasFunctorialCofiber.cofib (𝟙 X - p • g)
  obtain ⟨r, hr⟩ := postcomp_nsmul_id_surjective_cofiber_one_sub_nsmul p g Y (𝟙 Y)
  have hl : (p • 𝟙 Y) ≫ r = 𝟙 Y := by
    simpa only [Preadditive.nsmul_comp, Preadditive.comp_nsmul,
      Category.id_comp, Category.comp_id] using hr
  exact ⟨⟨r, hl, hr⟩⟩

end ScalarCofiber

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [HasProductsOfShape ℕ C]

omit [HasFunctorialCofiber (C := C)] in
/-- The residual Milnor map is literally `1 - p shift` on the product. -/
theorem scalarResidualSequence_oneSubShift (p : ℕ) (X : C) :
    (scalarResidualSequence p X).oneSubShift =
      𝟙 _ - p • (scalarResidualSequence 1 X).shiftMap := by
  apply congrArg (fun a => 𝟙 _ - a)
  apply Pi.hom_ext
  intro k
  simp only [InverseSequence.shiftMap, Pi.lift_π, Preadditive.nsmul_comp,
    scalarResidualSequence, one_smul, Category.comp_id, Preadditive.comp_nsmul]

/-- The homotopy limit of the scalar residual tower has invertible scalar
action. This supplies the acyclic term in the completion-unit comparison. -/
theorem scalarResidualSequence_homotopyLimit_isIso_nsmul (p : ℕ) (X : C) :
    IsIso (p • 𝟙 (scalarResidualSequence p X).homotopyLimit) := by
  have h := isIso_nsmul_id_cofiber_one_sub_nsmul p
    (scalarResidualSequence 1 X).shiftMap
  rw [← scalarResidualSequence_oneSubShift p X] at h
  letI := h
  exact isIso_nsmul_id_shift p
    (HasFunctorialCofiber.cofib (scalarResidualSequence p X).oneSubShift) (-1)

end KIP126.StableHomotopy
