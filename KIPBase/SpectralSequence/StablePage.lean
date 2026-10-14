/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import KIPBase.SpectralSequence.Blueprint
import KIPBase.SpectralSequence.ShiftedMorphism

/-!
# 扩张谱序列的稳定页映射

本文件证明：若一个有界扩张谱序列在第 `r` 页之前的微分全为零，
则其底层映射把过滤提高 `r`。对交换方块的两条竖边应用该结论，
得到从上边 ESS 到下边 ESS 的真正重指标谱序列态射。
-/

namespace KIPBase.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]

private theorem cycle_succ_eq_top_of_differential_eq_zero
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (E : SpectralSequence C ι) (r : ℤ) (k : ι) (hr : E.r₀ ≤ r)
    (hB : (E.ssData k).B
      (((r - E.r₀).toNat : ℕ) : WithTop ℕ) = ⊥)
    (hZ : (E.ssData k).Z
      (((r - E.r₀).toNat : ℕ) : WithTop ℕ) = ⊤)
    (hd : E.d r k = 0) :
    (E.ssData k).Z
      ((((r - E.r₀).toNat + 1 : ℕ)) : WithTop ℕ) = ⊤ := by
  let n := (r - E.r₀).toNat
  let D := E.ssData k
  let i := Subobject.ofLE (D.B (n : WithTop ℕ))
    (D.Z (n : WithTop ℕ)) (D.B_le_Z (n : WithTop ℕ))
  have hi : i = 0 := by
    apply (cancel_mono (D.Z (n : WithTop ℕ)).arrow).mp
    rw [Subobject.ofLE_arrow]
    rw [hB, Subobject.bot_arrow, zero_comp]
  let p := D.pageπ (n : WithTop ℕ)
  haveI hp : IsIso p := by
    change IsIso (cokernel.π i)
    rw [hi]
    infer_instance
  let j := Subobject.ofLE (D.Z ((n + 1 : ℕ) : WithTop ℕ))
    (D.Z (n : WithTop ℕ))
    (D.Z_anti (by exact_mod_cast Nat.le_succ n))
  have himage : imageSubobject (j ≫ p) = ⊤ := by
    have hs := E.Z_succ r k hr
    change kernelSubobject (E.d r k) = imageSubobject (j ≫ p) at hs
    rw [← hs, hd, kernelSubobject_zero]
  have himageIso : IsIso (imageSubobject (j ≫ p)).arrow := by
    rw [Subobject.isIso_arrow_iff_eq_top]
    exact himage
  letI := himageIso
  haveI himageEpi : Epi (imageSubobject (j ≫ p)).arrow := inferInstance
  haveI hcomp : Epi (j ≫ p) := by
    rw [← imageSubobject_arrow_comp (j ≫ p)]
    infer_instance
  haveI hjEpi : Epi j := (epi_comp_iff_of_isIso j p).mp inferInstance
  haveI hjIso : IsIso j := isIso_of_mono_of_epi j
  haveI hZnArrow : IsIso (D.Z (n : WithTop ℕ)).arrow := by
    rw [Subobject.isIso_arrow_iff_eq_top]
    exact hZ
  haveI hZsuccArrow :
      IsIso (D.Z ((n + 1 : ℕ) : WithTop ℕ)).arrow := by
    rw [show (D.Z ((n + 1 : ℕ) : WithTop ℕ)).arrow =
      j ≫ (D.Z (n : WithTop ℕ)).arrow by
        exact (Subobject.ofLE_arrow
          (D.Z_anti (by exact_mod_cast Nat.le_succ n))).symm]
    infer_instance
  exact Subobject.eq_top_of_isIso_arrow _

private theorem cycle_eq_top_of_differential_factors
    (FC : FilteredComplex C) (s k : ℤ) (n : ℕ)
    (hfac : ∃ φ : Subobject.underlying.obj (FC.fil s k) ⟶
        Subobject.underlying.obj (FC.fil (s + (n : ℤ)) (k - 1)),
      φ ≫ (FC.fil (s + (n : ℤ)) (k - 1)).arrow =
        (FC.fil s k).arrow ≫ FC.d k) :
    FC.cycleSubobject s k (n : WithTop ℕ) = ⊤ := by
  obtain ⟨φ, hφ⟩ := hfac
  let f := (FC.fil s k).arrow ≫ FC.d k ≫
    cokernel.π (FC.fil (s + (n : ℤ)) (k - 1)).arrow
  have hf : f = 0 := by
    dsimp only [f]
    rw [← Category.assoc, ← hφ, Category.assoc, cokernel.condition, comp_zero]
  change imageSubobject ((kernelSubobject f).arrow ≫
    FC.filToAssocGraded s k) = ⊤
  haveI hker : IsIso (kernelSubobject f).arrow := by
    rw [hf]
    infer_instance
  rw [imageSubobject_iso_comp]
  let p := cokernel.π (Subobject.ofLE (FC.fil (s + 1) k)
    (FC.fil s k) (FC.fil_anti s k))
  change imageSubobject p = ⊤
  haveI : Epi (image.ι p) := epi_image_of_epi _
  haveI : IsIso (image.ι p) := isIso_of_mono_of_epi _
  haveI : IsIso (imageSubobject p).arrow := by
    have h : IsIso ((imageSubobjectIso p).hom ≫ image.ι p) := inferInstance
    rw [imageSubobject_arrow] at h
    exact h
  exact Subobject.eq_top_of_isIso_arrow _

/-- 若次数 `k + 1` 到 `k` 的微分为零，则次数 `k` 的每个有限页边界子对象都为零。 -/
private theorem boundarySubobject_eq_bot_of_dToK_eq_zero
    (FC : FilteredComplex C) (s k : ℤ) (n : ℕ)
    (hd : FC.dToK k = 0) :
    FC.boundarySubobject s k (n : WithTop ℕ) = ⊥ := by
  let f := (FC.fil (s - (n : ℤ) + 1) (k + 1)).arrow ≫ FC.dToK k
  have hf : f = 0 := by
    dsimp only [f]
    rw [hd, comp_zero]
  have himg : imageSubobject f = ⊥ := by
    apply le_antisymm
    · apply imageSubobject_le f 0
      rw [zero_comp, hf]
    · exact bot_le
  simp only [FilteredComplex.boundarySubobject]
  change imageSubobject
    ((imageSubobject f ⊓ FC.fil s k).ofLE (FC.fil s k) _ ≫
      FC.filToAssocGraded s k) = ⊥
  let I := imageSubobject f ⊓ FC.fil s k
  have hI : I = ⊥ := by
    dsimp only [I]
    rw [himg, bot_inf_eq]
  let q := Subobject.ofLE I (FC.fil s k) inf_le_right
  change imageSubobject (q ≫ FC.filToAssocGraded s k) = ⊥
  have hbot : IsZero ((⊥ : Subobject (FC.A k)) : C) :=
    IsZero.of_iso (isZero_zero C) (Subobject.botCoeIsoZero (C := C))
  have hIZero : IsZero (I : C) :=
    IsZero.of_iso hbot (Subobject.isoOfEq I ⊥ hI)
  have hq : q = 0 := hIZero.eq_of_src _ _
  rw [hq, zero_comp, imageSubobject_zero]

/-- 两项过滤复形的微分在固定次数处把过滤提高 `n`。 -/
def BoundedExtensionSS.RaisesFiltrationAt
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι] {ω : Type w}
    {E₁ E₂ : SpectralSequence C ι}
    {A₁ A₂ : ω → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    {bnd₁ : F₁.IsBounded} {bnd₂ : F₂.IsBounded}
    (ext : BoundedExtensionSS conv₁ conv₂ cm bnd₁ bnd₂)
    (t : ω) (n : ℕ) : Prop :=
  ∀ s : ℤ, ∃ φ : Subobject.underlying.obj ((ext.complex t).fil s 1) ⟶
      Subobject.underlying.obj ((ext.complex t).fil (s + (n : ℤ)) (1 - 1)),
    φ ≫ ((ext.complex t).fil (s + (n : ℤ)) (1 - 1)).arrow =
      ((ext.complex t).fil s 1).arrow ≫ (ext.complex t).d 1

theorem BoundedExtensionSS.raisesFiltrationAt_zero
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι] {ω : Type w}
    {E₁ E₂ : SpectralSequence C ι}
    {A₁ A₂ : ω → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    {bnd₁ : F₁.IsBounded} {bnd₂ : F₂.IsBounded}
    (ext : BoundedExtensionSS conv₁ conv₂ cm bnd₁ bnd₂)
    (t : ω) : ext.RaisesFiltrationAt t 0 := by
  intro s
  rw [show s + ((0 : ℕ) : ℤ) = s by omega]
  exact (ext.complex t).d_preserves_fil s 1

theorem BoundedExtensionSS.raisesFiltrationAt_succ
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι] {ω : Type w}
    {E₁ E₂ : SpectralSequence C ι}
    {A₁ A₂ : ω → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    {bnd₁ : F₁.IsBounded} {bnd₂ : F₂.IsBounded}
    (ext : BoundedExtensionSS conv₁ conv₂ cm bnd₁ bnd₂)
    (t : ω) (n : ℕ) (hraise : ext.RaisesFiltrationAt t n)
    (hd : ∀ s : ℤ, ext.essDiff t (n : ℤ) (s, 1) = 0) :
    ext.RaisesFiltrationAt t (n + 1) := by
  intro s
  let FC := ext.complex t
  have hZn : FC.cycleSubobject s 1 (n : WithTop ℕ) = ⊤ :=
    cycle_eq_top_of_differential_factors FC s 1 n (hraise s)
  have hBn : ((ext.ess t).ssData (s, 1)).B
      (n : WithTop ℕ) = ⊥ := by
    change (ext.complex t).boundarySubobject s 1 (n : WithTop ℕ) = ⊥
    apply boundarySubobject_eq_bot_of_dToK_eq_zero
    simp [FilteredComplex.dToK, BoundedExtensionSS.complex,
      underlyingComplex, twoTermObj, twoTermDiff]
  have hdn : (ext.ess t).d (n : ℤ) (s, 1) = 0 := hd s
  have hZsucc : FC.cycleSubobject s 1
      ((n + 1 : ℕ) : WithTop ℕ) = ⊤ := by
    exact cycle_succ_eq_top_of_differential_eq_zero
      (ext.ess t) (n : ℤ) (s, 1)
        (by change (0 : ℤ) ≤ (n : ℤ); exact Int.natCast_nonneg n)
        hBn hZn hdn
  have htarget : s + 1 + (n : ℤ) = s + ((n + 1 : ℕ) : ℤ) := by omega
  let target := FC.fil (s + 1 + (n : ℤ)) (1 - 1)
  let f := (FC.fil s 1).arrow ≫ FC.d 1 ≫ cokernel.π target.arrow
  let K := kernelSubobject f
  let p := FC.filToAssocGraded s 1
  have hImage : imageSubobject (K.arrow ≫ p) = ⊤ := by
    change imageSubobject ((kernelSubobject
      ((FC.fil s 1).arrow ≫ FC.d 1 ≫
        cokernel.π (FC.fil (s + ((n + 1 : ℕ) : ℤ)) (1 - 1)).arrow)).arrow ≫
      FC.filToAssocGraded s 1) = ⊤ at hZsucc
    rw [← htarget] at hZsucc
    exact hZsucc
  let i := Subobject.ofLE (FC.fil (s + 1) 1) (FC.fil s 1)
    (FC.fil_anti s 1)
  obtain ⟨φ, hφ⟩ := hraise (s + 1)
  have hφ' : φ ≫ target.arrow =
      (FC.fil (s + 1) 1).arrow ≫ FC.d 1 := by
    exact hφ
  have hiZero : i ≫ f = 0 := by
    calc
      i ≫ f = ((i ≫ (FC.fil s 1).arrow) ≫ FC.d 1) ≫
          cokernel.π target.arrow := by simp only [f, Category.assoc]
      _ = ((FC.fil (s + 1) 1).arrow ≫ FC.d 1) ≫
          cokernel.π target.arrow := by rw [Subobject.ofLE_arrow]
      _ = (φ ≫ target.arrow) ≫ cokernel.π target.arrow := by rw [hφ']
      _ = 0 := by simp only [Category.assoc, cokernel.condition, comp_zero]
  let a := factorThruKernelSubobject f i hiZero
  have ha : a ≫ K.arrow = i :=
    factorThruKernelSubobject_comp_arrow f i hiZero
  have hImageIso : IsIso (imageSubobject (K.arrow ≫ p)).arrow := by
    rw [Subobject.isIso_arrow_iff_eq_top]
    exact hImage
  letI := hImageIso
  haveI hImageEpi : Epi (imageSubobject (K.arrow ≫ p)).arrow := inferInstance
  haveI hKpEpi : Epi (K.arrow ≫ p) := by
    rw [← imageSubobject_arrow_comp (K.arrow ≫ p)]
    infer_instance
  haveI hKEpi : Epi K.arrow := by
    apply Preadditive.epi_of_cancel_zero K.arrow
    intro R g hg
    have hig : i ≫ g = 0 := by
      rw [← ha, Category.assoc, hg, comp_zero]
    let d := cokernel.desc i g hig
    have hpd : p ≫ d = g := by
      exact cokernel.π_desc i g hig
    have hdZero : d = 0 := by
      apply zero_of_epi_comp (K.arrow ≫ p)
      rw [Category.assoc, hpd, hg]
    calc
      g = p ≫ d := hpd.symm
      _ = p ≫ (0 : cokernel i ⟶ R) :=
        congrArg (fun q : cokernel i ⟶ R => p ≫ q) hdZero
      _ = 0 := comp_zero
  have hKZero : f = 0 := zero_of_epi_comp K.arrow
    (kernelSubobject_arrow_comp f)
  have hresult : ∃ ψ : Subobject.underlying.obj (FC.fil s 1) ⟶
      Subobject.underlying.obj target,
    ψ ≫ target.arrow = (FC.fil s 1).arrow ≫ FC.d 1 := by
    refine ⟨Abelian.monoLift target.arrow
      ((FC.fil s 1).arrow ≫ FC.d 1) ?_, ?_⟩
    · simpa only [f, Category.assoc] using hKZero
    · exact Abelian.monoLift_comp _ _ _
  rw [show s + ((n + 1 : ℕ) : ℤ) = s + 1 + (n : ℤ) by omega]
  exact hresult

/-- 在第 `r` 页之前无 ESS 微分，意为所有 `n < r` 的页微分均为零。 -/
def BoundedExtensionSS.HasNoDifferentialBefore
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι] {ω : Type w}
    {E₁ E₂ : SpectralSequence C ι}
    {A₁ A₂ : ω → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    {bnd₁ : F₁.IsBounded} {bnd₂ : F₂.IsBounded}
    (ext : BoundedExtensionSS conv₁ conv₂ cm bnd₁ bnd₂)
    (t : ω) (r : ℕ) : Prop :=
  ∀ (n : ℕ), n < r → ∀ k : ℤ × ℤ,
    ext.essDiff t (n : ℤ) k = 0

theorem BoundedExtensionSS.raisesFiltrationAt_of_noDifferentialBefore
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι] {ω : Type w}
    {E₁ E₂ : SpectralSequence C ι}
    {A₁ A₂ : ω → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    {bnd₁ : F₁.IsBounded} {bnd₂ : F₂.IsBounded}
    (ext : BoundedExtensionSS conv₁ conv₂ cm bnd₁ bnd₂)
    (t : ω) (r : ℕ) (h : ext.HasNoDifferentialBefore t r) :
    ext.RaisesFiltrationAt t r := by
  induction r with
  | zero => exact ext.raisesFiltrationAt_zero t
  | succ n ih =>
      apply ext.raisesFiltrationAt_succ t n
      · exact ih (fun m hm => h m (Nat.lt_trans hm (Nat.lt_succ_self n)))
      · intro s
        exact h n (Nat.lt_succ_self n) (s, 1)

/-- ESS 在第 `r` 页之前无微分时，底层映射把第 `s` 层送入第
`s+r` 层。 -/
theorem BoundedExtensionSS.filtration_shift_of_noDifferentialBefore
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι] {ω : Type w}
    {E₁ E₂ : SpectralSequence C ι}
    {A₁ A₂ : ω → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    {bnd₁ : F₁.IsBounded} {bnd₂ : F₂.IsBounded}
    (ext : BoundedExtensionSS conv₁ conv₂ cm bnd₁ bnd₂)
    (t : ω) (r : ℕ) (h : ext.HasNoDifferentialBefore t r) (s : ℤ) :
    ∃ φ : Subobject.underlying.obj (F₁.F s t) ⟶
        Subobject.underlying.obj (F₂.F (s + (r : ℤ)) t),
      φ ≫ (F₂.F (s + (r : ℤ)) t).arrow =
        (F₁.F s t).arrow ≫ cm.aMap t := by
  have hraise := ext.raisesFiltrationAt_of_noDifferentialBefore t r h s
  simpa [BoundedExtensionSS.complex, underlyingComplex, twoTermFil,
    twoTermDiff, twoTermObj] using hraise

/-- 交换方块的 `p`-ESS 与 `q`-ESS 在第 `r` 页之前均无微分时，
两条竖边共同把过滤提高 `r`，因而在每一页给出从 `f`-ESS
到 `g`-ESS 的重指标页映射 `(s,k) ↦ (s+r,k)`。 -/
noncomputable def HomotopyCommSquare.stablePageESSReindexedPageMap
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι] {ω : Type w}
    {E₁ E₂ E₃ E₄ : SpectralSequence C ι}
    {A₁ A₂ A₃ A₄ : ω → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {F₃ : Filtration A₃} {F₄ : Filtration A₄}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {conv₃ : Convergence E₃ A₃ F₃} {conv₄ : Convergence E₄ A₄ F₄}
    (sq : HomotopyCommSquare conv₁ conv₂ conv₃ conv₄)
    (r : ℕ)
    (hp : ∀ t, sq.extp.HasNoDifferentialBefore t r)
    (hq : ∀ t, sq.extq.HasNoDifferentialBefore t r)
    (t : ω) (q : ℤ) (sk : ℤ × ℤ) :
    (sq.extf.ess t).Page q sk ⟶
      (sq.extg.ess t).Page q (sk.1 + (r : ℤ), sk.2) :=
  sq.shiftedESSReindexedPageMap (r : ℤ)
    { left := fun s t =>
        sq.extp.filtration_shift_of_noDifferentialBefore t r (hp t) s
      right := fun s t =>
        sq.extq.filtration_shift_of_noDifferentialBefore t r (hq t) s }
    t q sk

end KIPBase.SpectralSequence
