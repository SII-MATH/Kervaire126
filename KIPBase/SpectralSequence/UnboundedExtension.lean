/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Unbounded extension spectral sequence via truncation and stabilization.
Reference: informal/unbounded_extension.md
-/

import KIPBase.SpectralSequence.BoundedExtension
import KIPBase.SpectralSequence.Completion

universe u v w w₀

namespace KIPBase.SpectralSequence

open CategoryTheory CategoryTheory.Limits
open scoped Pseudoelement

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
variable {ω' : Type w}
variable {E₁ E₂ : SpectralSequence C ω}
variable {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
variable {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}

/-! ### 无界 ESS 的固定环境对象

无界 ESS 不能把某个截断层的关联分次当作环境对象。对固定的茎次数
`t`，次数 `1` 和 `0` 的环境对象分别是两个输入谱序列的原始 `E∞`
分量。后续的循环、边缘和页对象都必须作为这个固定环境对象中的子对象
来构造。 -/

/-- 收敛数据的重指标双射。 -/
noncomputable def Convergence.reindexEquiv
    {E : SpectralSequence C ω} {A : ω' → C} {F : Filtration A}
    (conv : Convergence E A F) : ω ≃ ℤ × ω' :=
  Equiv.ofBijective conv.reindex conv.reindex_bijective

/-- 无界 ESS 在 `(s,k)` 处的固定环境对象。

* `k = 1` 时取 `E₁` 在重指标 `(s,t)` 处的原始 `E∞` 项；
* `k = 0` 时取 `E₂` 在重指标 `(s,t)` 处的原始 `E∞` 项；
* 其余复形次数取零对象。

截断 ESS 只用于在这些固定对象内构造稳定的 `Z/B` 塔，不用来
替换此环境对象。 -/
noncomputable def unboundedExtensionV
    (conv₁ : Convergence E₁ A₁ F₁) (conv₂ : Convergence E₂ A₂ F₂)
    (t : ω') : ℤ × ℤ → C :=
  fun sk =>
    if sk.2 = 1 then
      (E₁.ssData (conv₁.reindexEquiv.symm (sk.1, t))).eInfty
    else if sk.2 = 0 then
      (E₂.ssData (conv₂.reindexEquiv.symm (sk.1, t))).eInfty
    else
      ⊥_ C

/-- 次数 `1` 的固定环境对象与 `F₁` 关联分次之间的收敛同构。 -/
noncomputable def unboundedExtensionVOneIso
    (conv₁ : Convergence E₁ A₁ F₁) (conv₂ : Convergence E₂ A₂ F₂)
    (t : ω') (s : ℤ) :
    unboundedExtensionV conv₁ conv₂ t (s, 1) ≅ F₁.associatedGraded s t := by
  dsimp [unboundedExtensionV]
  let i := conv₁.reindexEquiv.symm (s, t)
  have hi : conv₁.reindex i = (s, t) := by
    change conv₁.reindexEquiv i = (s, t)
    exact conv₁.reindexEquiv.apply_symm_apply (s, t)
  have e := conv₁.iso i
  rw [hi] at e
  exact e

/-- 次数 `0` 的固定环境对象与 `F₂` 关联分次之间的收敛同构。 -/
noncomputable def unboundedExtensionVZeroIso
    (conv₁ : Convergence E₁ A₁ F₁) (conv₂ : Convergence E₂ A₂ F₂)
    (t : ω') (s : ℤ) :
    unboundedExtensionV conv₁ conv₂ t (s, 0) ≅ F₂.associatedGraded s t := by
  dsimp [unboundedExtensionV]
  let i := conv₂.reindexEquiv.symm (s, t)
  have hi : conv₂.reindex i = (s, t) := by
    change conv₂.reindexEquiv i = (s, t)
    exact conv₂.reindexEquiv.apply_symm_apply (s, t)
  have e := conv₂.iso i
  rw [hi] at e
  exact e

/-- 未截断的两项过滤复形。它只提供有限页的循环、边缘和微分数据；
其环境对象随后通过收敛同构识别为输入谱序列的原始 `E∞` 项。 -/
noncomputable def unboundedUnderlyingComplex
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω') : FilteredComplex C :=
  underlyingComplex cm.aMap cm.filtration_compat t

private theorem unboundedUC_assocGraded_one
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω') (s : ℤ) :
    (unboundedUnderlyingComplex cm t).assocGraded s 1 =
      F₁.associatedGraded s t := by
  simp only [unboundedUnderlyingComplex, underlyingComplex,
    FilteredComplex.assocGraded, Filtration.associatedGraded, twoTermFil]
  congr 1

private theorem unboundedUC_assocGraded_zero
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω') (s : ℤ) :
    (unboundedUnderlyingComplex cm t).assocGraded s 0 =
      F₂.associatedGraded s t := by
  simp only [unboundedUnderlyingComplex, underlyingComplex,
    FilteredComplex.assocGraded, Filtration.associatedGraded, twoTermFil]
  congr 1

/-- 次数 `1` 的原始 `E₁∞` 环境对象与未截断两项复形关联分次的同构。 -/
noncomputable def unboundedExtensionVOneComplexIso
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω') (s : ℤ) :
    unboundedExtensionV conv₁ conv₂ t (s, 1) ≅
      (unboundedUnderlyingComplex cm t).assocGraded s 1 :=
  unboundedExtensionVOneIso conv₁ conv₂ t s ≪≫
    eqToIso (unboundedUC_assocGraded_one cm t s).symm

/-- 次数 `0` 的原始 `E₂∞` 环境对象与未截断两项复形关联分次的同构。 -/
noncomputable def unboundedExtensionVZeroComplexIso
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω') (s : ℤ) :
    unboundedExtensionV conv₁ conv₂ t (s, 0) ≅
      (unboundedUnderlyingComplex cm t).assocGraded s 0 :=
  unboundedExtensionVZeroIso conv₁ conv₂ t s ≪≫
    eqToIso (unboundedUC_assocGraded_zero cm t s).symm

/-- 在两项复形次数之外，未截断底层复形的对象为零。 -/
private theorem unboundedUC_obj_other
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω') (k : ℤ)
    (h₁ : k ≠ 1) (h₀ : k ≠ 0) :
    (unboundedUnderlyingComplex cm t).A k = ⊥_ C := by
  simp [unboundedUnderlyingComplex, underlyingComplex, twoTermObj, h₁, h₀]

/-- 两项复形次数之外，未截断复形的关联分次为零对象。 -/
private theorem unboundedUC_assocGraded_isZero_other
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω') (s k : ℤ)
    (h₁ : k ≠ 1) (h₀ : k ≠ 0) :
    IsZero ((unboundedUnderlyingComplex cm t).assocGraded s k) := by
  have hA : IsZero ((unboundedUnderlyingComplex cm t).A k) := by
    rw [unboundedUC_obj_other cm t k h₁ h₀]
    exact IsInitial.isZero initialIsInitial
  have hFil : IsZero
      (Subobject.underlying.obj ((unboundedUnderlyingComplex cm t).fil s k)) :=
    hA.of_mono ((unboundedUnderlyingComplex cm t).fil s k).arrow
  exact hFil.of_epi (cokernel.π (Subobject.ofLE
    ((unboundedUnderlyingComplex cm t).fil (s + 1) k)
    ((unboundedUnderlyingComplex cm t).fil s k)
    ((unboundedUnderlyingComplex cm t).fil_anti s k)))

/-- 原始 `E∞` 环境对象与未截断两项复形关联分次的逐次数同构。 -/
noncomputable def unboundedExtensionVComplexIso
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω') (s k : ℤ) :
    unboundedExtensionV conv₁ conv₂ t (s, k) ≅
      (unboundedUnderlyingComplex cm t).assocGraded s k := by
  by_cases h₁ : k = 1
  · subst h₁
    exact unboundedExtensionVOneComplexIso cm t s
  by_cases h₀ : k = 0
  · subst h₀
    exact unboundedExtensionVZeroComplexIso cm t s
  · have hV : IsZero (unboundedExtensionV conv₁ conv₂ t (s, k)) := by
      simp only [unboundedExtensionV, h₁, h₀, ↓reduceIte]
      exact IsInitial.isZero initialIsInitial
    have hA : IsZero ((unboundedUnderlyingComplex cm t).A k) := by
      rw [unboundedUC_obj_other cm t k h₁ h₀]
      exact IsInitial.isZero initialIsInitial
    have hFil : IsZero
        (Subobject.underlying.obj ((unboundedUnderlyingComplex cm t).fil s k)) :=
      hA.of_mono ((unboundedUnderlyingComplex cm t).fil s k).arrow
    have hGr : IsZero ((unboundedUnderlyingComplex cm t).assocGraded s k) := by
      exact hFil.of_epi (cokernel.π (Subobject.ofLE
        ((unboundedUnderlyingComplex cm t).fil (s + 1) k)
        ((unboundedUnderlyingComplex cm t).fil s k)
        ((unboundedUnderlyingComplex cm t).fil_anti s k)))
    exact IsZero.iso hV hGr

/-- 两条具有同一源收敛谱序列的边，在复形次数 `1` 使用同一个过滤层。 -/
theorem unboundedUnderlyingComplex_source_fil_eq
    {E₃ : SpectralSequence C ω} {A₃ : ω' → C} {F₃ : Filtration A₃}
    {conv₃ : Convergence E₃ A₃ F₃}
    (cm₁ : ConvergenceMorphism conv₁ conv₂)
    (cm₂ : ConvergenceMorphism conv₁ conv₃) (t : ω') (s : ℤ) :
    (unboundedUnderlyingComplex cm₁ t).fil s 1 =
      (unboundedUnderlyingComplex cm₂ t).fil s 1 := by
  rfl

/-- 同源两条边在次数 `1` 的原始 `E∞`—关联分次同构相同。 -/
theorem unboundedExtensionVComplexIso_source_hom_eq
    {E₃ : SpectralSequence C ω} {A₃ : ω' → C} {F₃ : Filtration A₃}
    {conv₃ : Convergence E₃ A₃ F₃}
    (cm₁ : ConvergenceMorphism conv₁ conv₂)
    (cm₂ : ConvergenceMorphism conv₁ conv₃) (t : ω') (s : ℤ) :
    (unboundedExtensionVComplexIso cm₁ t s 1).hom =
      (unboundedExtensionVComplexIso cm₂ t s 1).hom := by
  change (unboundedExtensionVOneComplexIso cm₁ t s).hom =
    (unboundedExtensionVOneComplexIso cm₂ t s).hom
  simp only [unboundedExtensionVOneComplexIso, unboundedExtensionVOneIso,
    Iso.trans_hom]

/-- 可复合两条边在公共顶点使用同一个过滤层：前一条边的次数 `0`
与后一条边的次数 `1` 都是中间对象的过滤。 -/
theorem unboundedUnderlyingComplex_target_source_fil_eq
    {E₃ : SpectralSequence C ω} {A₃ : ω' → C} {F₃ : Filtration A₃}
    {conv₃ : Convergence E₃ A₃ F₃}
    (cm₁ : ConvergenceMorphism conv₁ conv₂)
    (cm₂ : ConvergenceMorphism conv₂ conv₃) (t : ω') (s : ℤ) :
    (unboundedUnderlyingComplex cm₁ t).fil s 0 =
      (unboundedUnderlyingComplex cm₂ t).fil s 1 := by
  rfl

/-- 可复合两条边在公共顶点使用同一个原始 `E∞`—关联分次同构。 -/
theorem unboundedExtensionVComplexIso_target_source_hom_eq
    {E₃ : SpectralSequence C ω} {A₃ : ω' → C} {F₃ : Filtration A₃}
    {conv₃ : Convergence E₃ A₃ F₃}
    (cm₁ : ConvergenceMorphism conv₁ conv₂)
    (cm₂ : ConvergenceMorphism conv₂ conv₃) (t : ω') (s : ℤ) :
    (unboundedExtensionVComplexIso cm₁ t s 0).hom =
      (unboundedExtensionVComplexIso cm₂ t s 1).hom := by
  change (unboundedExtensionVZeroComplexIso cm₁ t s).hom =
    (unboundedExtensionVOneComplexIso cm₂ t s).hom
  simp only [unboundedExtensionVZeroComplexIso, unboundedExtensionVOneComplexIso,
    unboundedExtensionVZeroIso, unboundedExtensionVOneIso, Iso.trans_hom]

/-- 两条具有同一目标收敛谱序列的边，在次数 `0` 使用同一个过滤层。 -/
theorem unboundedUnderlyingComplex_target_fil_eq
    {E₀ : SpectralSequence C ω} {A₀ : ω' → C} {F₀ : Filtration A₀}
    {conv₀ : Convergence E₀ A₀ F₀}
    (cm₁ : ConvergenceMorphism conv₁ conv₂)
    (cm₂ : ConvergenceMorphism conv₀ conv₂) (t : ω') (s : ℤ) :
    (unboundedUnderlyingComplex cm₁ t).fil s 0 =
      (unboundedUnderlyingComplex cm₂ t).fil s 0 := by
  rfl

/-- 同目标两条边在次数 `0` 的原始 `E∞`—关联分次同构相同。 -/
theorem unboundedExtensionVComplexIso_target_hom_eq
    {E₀ : SpectralSequence C ω} {A₀ : ω' → C} {F₀ : Filtration A₀}
    {conv₀ : Convergence E₀ A₀ F₀}
    (cm₁ : ConvergenceMorphism conv₁ conv₂)
    (cm₂ : ConvergenceMorphism conv₀ conv₂) (t : ω') (s : ℤ) :
    (unboundedExtensionVComplexIso cm₁ t s 0).hom =
      (unboundedExtensionVComplexIso cm₂ t s 0).hom := by
  change (unboundedExtensionVZeroComplexIso cm₁ t s).hom =
    (unboundedExtensionVZeroComplexIso cm₂ t s).hom
  simp only [unboundedExtensionVZeroComplexIso, unboundedExtensionVZeroIso,
    Iso.trans_hom]

/-- 由同一环境对象中的有限 `Z/B` 塔组装 `SSData`。
无穷循环层取有限循环层的下确界，无穷边缘层取有限边缘层的
上确界；因此 `E∞` 仍在原始环境对象内定义。 -/
private noncomputable def ssDataOfNatTower
    (V : C) [LocallySmall.{w₀} C] [WellPowered.{w₀} C]
    [HasWidePullbacks.{w₀} C] [HasCoproducts.{w₀} C]
    (Z B : ℕ → Subobject V)
    (hZ : ∀ {m n : ℕ}, m ≤ n → Z n ≤ Z m)
    (hB : ∀ {m n : ℕ}, m ≤ n → B m ≤ B n)
    (hZ₀ : Z 0 = ⊤)
    (hBZ : ∀ m n : ℕ, B m ≤ Z n) : SSData C where
  V := V
  Z := fun r => r.recTopCoe (Subobject.sInf (Set.range Z)) Z
  B := fun r => r.recTopCoe (Subobject.sSup (Set.range B)) B
  Z_anti := by
    intro a b hab
    cases a with
    | top =>
        cases b with
        | top => exact le_rfl
        | coe n => exact absurd hab (WithTop.not_top_le_coe n)
    | coe m =>
        cases b with
        | top =>
            change Subobject.sInf (Set.range Z) ≤ Z m
            exact Subobject.sInf_le _ _ ⟨m, rfl⟩
        | coe n =>
            change Z n ≤ Z m
            exact hZ (WithTop.coe_le_coe.mp hab)
  B_mono := by
    intro a b hab
    cases a with
    | top =>
        cases b with
        | top => exact le_rfl
        | coe n => exact absurd hab (WithTop.not_top_le_coe n)
    | coe m =>
        cases b with
        | top =>
            change B m ≤ Subobject.sSup (Set.range B)
            exact Subobject.le_sSup _ _ ⟨m, rfl⟩
        | coe n =>
            change B m ≤ B n
            exact hB (WithTop.coe_le_coe.mp hab)
  Z_zero := by
    change Z 0 = ⊤
    exact hZ₀
  B_le_Z := by
    intro r
    cases r with
    | top =>
        change Subobject.sSup (Set.range B) ≤ Subobject.sInf (Set.range Z)
        apply Subobject.sSup_le
        intro b hb
        obtain ⟨m, rfl⟩ := hb
        apply Subobject.le_sInf
        intro z hz
        obtain ⟨n, rfl⟩ := hz
        exact hBZ m n
    | coe n =>
        change B n ≤ Z n
        exact hBZ n n
  Z_top_greatest := by
    intro X hX
    change X ≤ Subobject.sInf (Set.range Z)
    apply Subobject.le_sInf
    intro z hz
    obtain ⟨n, rfl⟩ := hz
    exact hX n
  B_top_least := by
    intro X hX
    change Subobject.sSup (Set.range B) ≤ X
    apply Subobject.sSup_le
    intro b hb
    obtain ⟨n, rfl⟩ := hb
    exact hX n

/-- 过滤复形的任意有限边缘层都包含于任意有限循环层。 -/
private theorem FilteredComplex.boundary_le_cycle_nat
    (FC : FilteredComplex C) (s k : ℤ) (m n : ℕ) :
    FC.boundarySubobject s k (m : WithTop ℕ) ≤
      FC.cycleSubobject s k (n : WithTop ℕ) := by
  rcases le_total m n with hmn | hnm
  · exact le_trans (FC.boundarySubobject_nat_mono s k hmn)
      (FC.B_le_Z_aux s k n)
  · exact le_trans (FC.B_le_Z_aux s k m)
      (FC.cycleSubobject_nat_anti s k hnm)

/-- 次数 `1` 处搬回原始 `E₁∞` 环境对象的有限循环层。 -/
private noncomputable def unboundedCycleOne
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω') (s : ℤ) (n : ℕ) :
    Subobject (unboundedExtensionV conv₁ conv₂ t (s, 1)) :=
  (Subobject.mapIsoToOrderIso (unboundedExtensionVOneComplexIso cm t s)).symm
    ((unboundedUnderlyingComplex cm t).cycleSubobject s 1 (n : WithTop ℕ))

/-- 次数 `0` 处搬回原始 `E₂∞` 环境对象的有限边缘层。 -/
private noncomputable def unboundedBoundaryZero
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω') (s : ℤ) (n : ℕ) :
    Subobject (unboundedExtensionV conv₁ conv₂ t (s, 0)) :=
  (Subobject.mapIsoToOrderIso (unboundedExtensionVZeroComplexIso cm t s)).symm
    ((unboundedUnderlyingComplex cm t).boundarySubobject s 0 (n : WithTop ℕ))

section SubobjectLimits

variable [LocallySmall.{w₀} C] [WellPowered.{w₀} C]
variable [HasWidePullbacks.{w₀} C] [HasCoproducts.{w₀} C]

/-- 未截断复形的有限 `Z/B` 塔在其自身关联分次上组成的数据。 -/
noncomputable def unboundedComplexSSData
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω') (s k : ℤ) : SSData C :=
  ssDataOfNatTower
    ((unboundedUnderlyingComplex cm t).assocGraded s k)
    (fun n => (unboundedUnderlyingComplex cm t).cycleSubobject s k n)
    (fun n => (unboundedUnderlyingComplex cm t).boundarySubobject s k n)
    (fun h => (unboundedUnderlyingComplex cm t).cycleSubobject_nat_anti s k h)
    (fun h => (unboundedUnderlyingComplex cm t).boundarySubobject_nat_mono s k h)
    ((unboundedUnderlyingComplex cm t).cycleSubobject_zero_eq_top s k)
    (fun m n => (unboundedUnderlyingComplex cm t).boundary_le_cycle_nat s k m n)

/-- 把未截断复形的有限循环层沿原始 `E∞` 环境同构搬回。 -/
noncomputable def unboundedExtensionZ
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω') (s k : ℤ) (n : ℕ) :
    Subobject (unboundedExtensionV conv₁ conv₂ t (s, k)) :=
  (Subobject.mapIsoToOrderIso (unboundedExtensionVComplexIso cm t s k)).symm
    ((unboundedUnderlyingComplex cm t).cycleSubobject s k n)

/-- 把未截断复形的有限边缘层沿原始 `E∞` 环境同构搬回。 -/
noncomputable def unboundedExtensionB
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω') (s k : ℤ) (n : ℕ) :
    Subobject (unboundedExtensionV conv₁ conv₂ t (s, k)) :=
  (Subobject.mapIsoToOrderIso (unboundedExtensionVComplexIso cm t s k)).symm
    ((unboundedUnderlyingComplex cm t).boundarySubobject s k n)

/-- 环境同构把无界有限循环层送回未截断复形的循环层。 -/
@[simp]
theorem unboundedExtensionZ_map
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω')
    (s k : ℤ) (n : ℕ) :
    (Subobject.mapIsoToOrderIso (unboundedExtensionVComplexIso cm t s k))
        (unboundedExtensionZ cm t s k n) =
      (unboundedUnderlyingComplex cm t).cycleSubobject s k n :=
  (Subobject.mapIsoToOrderIso
    (unboundedExtensionVComplexIso cm t s k)).apply_symm_apply _

/-- 环境同构把无界有限边缘层送回未截断复形的边缘层。 -/
@[simp]
theorem unboundedExtensionB_map
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω')
    (s k : ℤ) (n : ℕ) :
    (Subobject.mapIsoToOrderIso (unboundedExtensionVComplexIso cm t s k))
        (unboundedExtensionB cm t s k n) =
      (unboundedUnderlyingComplex cm t).boundarySubobject s k n :=
  (Subobject.mapIsoToOrderIso
    (unboundedExtensionVComplexIso cm t s k)).apply_symm_apply _

/-- 在原始 `E∞` 环境对象内由搬回的有限 `Z/B` 塔组成数据。 -/
private noncomputable def unboundedSSData
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω') (s k : ℤ) : SSData C :=
  ssDataOfNatTower
    (unboundedExtensionV conv₁ conv₂ t (s, k))
    (unboundedExtensionZ cm t s k)
    (unboundedExtensionB cm t s k)
    (fun h =>
      (Subobject.mapIsoToOrderIso
        (unboundedExtensionVComplexIso cm t s k)).symm.monotone
          ((unboundedUnderlyingComplex cm t).cycleSubobject_nat_anti s k h))
    (fun h =>
      (Subobject.mapIsoToOrderIso
        (unboundedExtensionVComplexIso cm t s k)).symm.monotone
          ((unboundedUnderlyingComplex cm t).boundarySubobject_nat_mono s k h))
    (by
      unfold unboundedExtensionZ
      rw [(unboundedUnderlyingComplex cm t).cycleSubobject_zero_eq_top s k]
      exact OrderIso.map_top _)
    (fun m n =>
      (Subobject.mapIsoToOrderIso
        (unboundedExtensionVComplexIso cm t s k)).symm.monotone
          ((unboundedUnderlyingComplex cm t).boundary_le_cycle_nat s k m n))

/-- 无界 ESS 在复形次数 `1` 处的 `SSData`。环境对象是原始 `E₁∞`，
有限循环层来自未截断两项复形，所有有限边缘层均为零。 -/
private noncomputable def unboundedSSDataOne
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω') (s : ℤ) : SSData C :=
  ssDataOfNatTower
    (unboundedExtensionV conv₁ conv₂ t (s, 1))
    (unboundedCycleOne cm t s)
    (fun _ => ⊥)
    (fun hmn =>
      (Subobject.mapIsoToOrderIso
        (unboundedExtensionVOneComplexIso cm t s)).symm.monotone
          ((unboundedUnderlyingComplex cm t).cycleSubobject_nat_anti s 1 hmn))
    (fun _ => le_rfl)
    (by
      unfold unboundedCycleOne
      rw [(unboundedUnderlyingComplex cm t).cycleSubobject_zero_eq_top s 1]
      exact OrderIso.map_top _)
    (fun _ _ => bot_le)

/-- 无界 ESS 在复形次数 `0` 处的 `SSData`。环境对象是原始 `E₂∞`，
所有有限循环层均为整个对象，有限边缘层来自未截断两项复形。 -/
private noncomputable def unboundedSSDataZero
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω') (s : ℤ) : SSData C :=
  ssDataOfNatTower
    (unboundedExtensionV conv₁ conv₂ t (s, 0))
    (fun _ => ⊤)
    (unboundedBoundaryZero cm t s)
    (fun _ => le_rfl)
    (fun hmn =>
      (Subobject.mapIsoToOrderIso
        (unboundedExtensionVZeroComplexIso cm t s)).symm.monotone
          ((unboundedUnderlyingComplex cm t).boundarySubobject_nat_mono s 0 hmn))
    rfl
    (fun _ _ => le_top)

/-- 零复形次数处的平凡 `SSData`。 -/
private noncomputable def zeroSSData : SSData C where
  V := ⊥_ C
  Z := fun _ => ⊤
  B := fun _ => ⊥
  Z_anti := fun _ _ _ => le_rfl
  B_mono := fun _ _ _ => le_rfl
  Z_zero := rfl
  B_le_Z := fun _ => bot_le
  Z_top_greatest := fun _ _ => le_top
  B_top_least := fun _ _ => bot_le

/-- 无界 ESS 的逐双次数 `SSData`。其 `V` 字段逐字来自
`unboundedExtensionV`，截断对象不参与环境对象的定义。 -/
noncomputable def unboundedExtensionSSData
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω') : ℤ × ℤ → SSData C :=
  fun ⟨s, k⟩ => unboundedSSData cm t s k

/-- 未截断复形自身关联分次上的逐双次数 `SSData`。 -/
noncomputable def unboundedComplexSSDataFamily
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω') : ℤ × ℤ → SSData C :=
  fun ⟨s, k⟩ => unboundedComplexSSData cm t s k

/-- 复形侧无界数据的有限循环层就是未截断过滤复形的有限循环层。 -/
@[simp]
theorem unboundedComplexSSDataFamily_Z_nat
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω')
    (s k : ℤ) (n : ℕ) :
    ((unboundedComplexSSDataFamily cm t (s, k)).Z (n : WithTop ℕ)) =
      (unboundedUnderlyingComplex cm t).cycleSubobject s k n :=
  rfl

/-- 复形侧无界数据的有限边缘层就是未截断过滤复形的有限边缘层。 -/
@[simp]
theorem unboundedComplexSSDataFamily_B_nat
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω')
    (s k : ℤ) (n : ℕ) :
    ((unboundedComplexSSDataFamily cm t (s, k)).B (n : WithTop ℕ)) =
      (unboundedUnderlyingComplex cm t).boundarySubobject s k n :=
  rfl

/-- 把未截断过滤复形中的源提升视为复形侧无界数据的有限循环层元素。 -/
noncomputable def unboundedComplexSourceCycleLift
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω')
    (s k : ℤ) (n : ℕ) {T : C}
    {xl : T ⟶ Subobject.underlying.obj ((unboundedUnderlyingComplex cm t).fil s k)}
    {yl : T ⟶ Subobject.underlying.obj
      ((unboundedUnderlyingComplex cm t).fil (s + (n : ℤ)) (k - 1))}
    (hd : xl ≫ (unboundedUnderlyingComplex cm t).filDiff s k =
      yl ≫ Subobject.ofLE
        ((unboundedUnderlyingComplex cm t).fil (s + (n : ℤ)) (k - 1))
        ((unboundedUnderlyingComplex cm t).fil s (k - 1))
        ((unboundedUnderlyingComplex cm t).fil_anti_of_le (k - 1) (by omega))) :
    T ⟶ Subobject.underlying.obj
      ((unboundedComplexSSDataFamily cm t (s, k)).Z (n : WithTop ℕ)) :=
  (unboundedUnderlyingComplex cm t).sourceCycleLift
    (n : ℤ) (Int.natCast_nonneg n) s k hd

/-- 把未截断过滤复形中的目标提升视为复形侧无界数据的有限循环层元素。 -/
noncomputable def unboundedComplexTargetCycleLift
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω')
    (s k : ℤ) (n : ℕ) {T : C}
    {xl : T ⟶ Subobject.underlying.obj ((unboundedUnderlyingComplex cm t).fil s k)}
    {yl : T ⟶ Subobject.underlying.obj
      ((unboundedUnderlyingComplex cm t).fil (s + (n : ℤ)) (k - 1))}
    (hd : xl ≫ (unboundedUnderlyingComplex cm t).filDiff s k =
      yl ≫ Subobject.ofLE
        ((unboundedUnderlyingComplex cm t).fil (s + (n : ℤ)) (k - 1))
        ((unboundedUnderlyingComplex cm t).fil s (k - 1))
        ((unboundedUnderlyingComplex cm t).fil_anti_of_le (k - 1) (by omega))) :
    T ⟶ Subobject.underlying.obj
      ((unboundedComplexSSDataFamily cm t (s + (n : ℤ), k - 1)).Z
        (n : WithTop ℕ)) :=
  (unboundedUnderlyingComplex cm t).targetCycleLift
    (n : ℤ) (Int.natCast_nonneg n) s k hd

/-- 源循环提升与复形侧无界数据的子对象箭头相容。 -/
theorem unboundedComplexSourceCycleLift_arrow
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω')
    (s k : ℤ) (n : ℕ) {T : C}
    {xl : T ⟶ Subobject.underlying.obj ((unboundedUnderlyingComplex cm t).fil s k)}
    {yl : T ⟶ Subobject.underlying.obj
      ((unboundedUnderlyingComplex cm t).fil (s + (n : ℤ)) (k - 1))}
    (hd : xl ≫ (unboundedUnderlyingComplex cm t).filDiff s k =
      yl ≫ Subobject.ofLE
        ((unboundedUnderlyingComplex cm t).fil (s + (n : ℤ)) (k - 1))
        ((unboundedUnderlyingComplex cm t).fil s (k - 1))
        ((unboundedUnderlyingComplex cm t).fil_anti_of_le (k - 1) (by omega))) :
    unboundedComplexSourceCycleLift cm t s k n hd ≫
        ((unboundedComplexSSDataFamily cm t (s, k)).Z (n : WithTop ℕ)).arrow =
      xl ≫ (unboundedUnderlyingComplex cm t).filToAssocGraded s k := by
  unfold unboundedComplexSourceCycleLift
  change (unboundedUnderlyingComplex cm t).sourceCycleLift
      (n : ℤ) (Int.natCast_nonneg n) s k hd ≫
        ((unboundedUnderlyingComplex cm t).cycleSubobject s k
          (n : WithTop ℕ)).arrow = _
  simpa only [Int.toNat_natCast] using
    (unboundedUnderlyingComplex cm t).sourceCycleLift_arrow
      (n : ℤ) (Int.natCast_nonneg n) s k hd

/-- 目标循环提升与复形侧无界数据的子对象箭头相容。 -/
theorem unboundedComplexTargetCycleLift_arrow
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω')
    (s k : ℤ) (n : ℕ) {T : C}
    {xl : T ⟶ Subobject.underlying.obj ((unboundedUnderlyingComplex cm t).fil s k)}
    {yl : T ⟶ Subobject.underlying.obj
      ((unboundedUnderlyingComplex cm t).fil (s + (n : ℤ)) (k - 1))}
    (hd : xl ≫ (unboundedUnderlyingComplex cm t).filDiff s k =
      yl ≫ Subobject.ofLE
        ((unboundedUnderlyingComplex cm t).fil (s + (n : ℤ)) (k - 1))
        ((unboundedUnderlyingComplex cm t).fil s (k - 1))
        ((unboundedUnderlyingComplex cm t).fil_anti_of_le (k - 1) (by omega))) :
    unboundedComplexTargetCycleLift cm t s k n hd ≫
        ((unboundedComplexSSDataFamily cm t (s + (n : ℤ), k - 1)).Z
          (n : WithTop ℕ)).arrow =
      yl ≫ (unboundedUnderlyingComplex cm t).filToAssocGraded
        (s + (n : ℤ)) (k - 1) := by
  unfold unboundedComplexTargetCycleLift
  change (unboundedUnderlyingComplex cm t).targetCycleLift
      (n : ℤ) (Int.natCast_nonneg n) s k hd ≫
        ((unboundedUnderlyingComplex cm t).cycleSubobject
          (s + (n : ℤ)) (k - 1) (n : WithTop ℕ)).arrow = _
  simpa only [Int.toNat_natCast] using
    (unboundedUnderlyingComplex cm t).targetCycleLift_arrow
      (n : ℤ) (Int.natCast_nonneg n) s k hd

/-- 环境同构把搬回的整条循环塔送回未截断复形的循环塔。 -/
private theorem unboundedExtensionSSData_map_Z
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω') (s k : ℤ)
    (r : WithTop ℕ) :
    (Subobject.mapIsoToOrderIso (unboundedExtensionVComplexIso cm t s k))
        ((unboundedSSData cm t s k).Z r) =
      (unboundedComplexSSData cm t s k).Z r := by
  cases r with
  | coe n =>
      exact (Subobject.mapIsoToOrderIso
        (unboundedExtensionVComplexIso cm t s k)).apply_symm_apply _
  | top =>
      simp only [unboundedSSData, unboundedComplexSSData, ssDataOfNatTower]
      rw [WithTop.recTopCoe_top, WithTop.recTopCoe_top]
      let O := Subobject.mapIsoToOrderIso (unboundedExtensionVComplexIso cm t s k)
      let P := unboundedExtensionZ cm t s k
      let Q := fun n : ℕ =>
        (unboundedUnderlyingComplex cm t).cycleSubobject s k (n : WithTop ℕ)
      change O (Subobject.sInf (Set.range P)) = Subobject.sInf (Set.range Q)
      have hPQ (n : ℕ) : O (P n) = Q n := by
        exact O.apply_symm_apply _
      apply le_antisymm
      · apply Subobject.le_sInf
        intro q hq
        obtain ⟨n, rfl⟩ := hq
        simpa only [hPQ n] using
          O.monotone (Subobject.sInf_le (Set.range P) (P n) ⟨n, rfl⟩)
      · have h : O.symm (Subobject.sInf (Set.range Q)) ≤
            Subobject.sInf (Set.range P) := by
          apply Subobject.le_sInf
          intro p hp
          obtain ⟨n, rfl⟩ := hp
          have hn := Subobject.sInf_le (Set.range Q) (Q n) ⟨n, rfl⟩
          calc
            O.symm (Subobject.sInf (Set.range Q)) ≤ O.symm (O (P n)) := by
              apply O.symm.monotone
              simpa only [hPQ n] using hn
            _ = P n := O.symm_apply_apply _
        simpa using O.monotone h

/-- 环境同构把搬回的整条边缘塔送回未截断复形的边缘塔。 -/
private theorem unboundedExtensionSSData_map_B
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω') (s k : ℤ)
    (r : WithTop ℕ) :
    (Subobject.mapIsoToOrderIso (unboundedExtensionVComplexIso cm t s k))
        ((unboundedSSData cm t s k).B r) =
      (unboundedComplexSSData cm t s k).B r := by
  cases r with
  | coe n =>
      exact (Subobject.mapIsoToOrderIso
        (unboundedExtensionVComplexIso cm t s k)).apply_symm_apply _
  | top =>
      simp only [unboundedSSData, unboundedComplexSSData, ssDataOfNatTower]
      rw [WithTop.recTopCoe_top, WithTop.recTopCoe_top]
      let O := Subobject.mapIsoToOrderIso (unboundedExtensionVComplexIso cm t s k)
      let P := unboundedExtensionB cm t s k
      let Q := fun n : ℕ =>
        (unboundedUnderlyingComplex cm t).boundarySubobject s k (n : WithTop ℕ)
      change O (Subobject.sSup (Set.range P)) = Subobject.sSup (Set.range Q)
      have hPQ (n : ℕ) : O (P n) = Q n := by
        exact O.apply_symm_apply _
      apply le_antisymm
      · have h : Subobject.sSup (Set.range P) ≤
            O.symm (Subobject.sSup (Set.range Q)) := by
          apply Subobject.sSup_le
          intro p hp
          obtain ⟨n, rfl⟩ := hp
          have hn := Subobject.le_sSup (Set.range Q) (Q n) ⟨n, rfl⟩
          calc
            P n = O.symm (O (P n)) := (O.symm_apply_apply _).symm
            _ ≤ O.symm (Subobject.sSup (Set.range Q)) := by
              apply O.symm.monotone
              simpa only [hPQ n] using hn
        simpa using O.monotone h
      · apply Subobject.sSup_le
        intro q hq
        obtain ⟨n, rfl⟩ := hq
        simpa only [hPQ n] using
          O.monotone (Subobject.le_sSup (Set.range P) (P n) ⟨n, rfl⟩)

/-- 若两个子对象在同构下对应，则其底层箭头经同构后穿过目标子对象。 -/
private theorem subobject_factors_of_mapIso_eq {X Y : C} (e : X ≅ Y)
    (P : Subobject X) (Q : Subobject Y)
    (h : (Subobject.mapIsoToOrderIso e) P = Q) :
    Q.Factors (P.arrow ≫ e.hom) := by
  rw [← h]
  have hm : Subobject.mk (P.arrow ≫ e.hom) =
      (Subobject.mapIsoToOrderIso e) P := by
    calc
      Subobject.mk (P.arrow ≫ e.hom) =
          (Subobject.map e.hom).obj (Subobject.mk P.arrow) :=
        (Subobject.map_mk P.arrow e.hom).symm
      _ = (Subobject.map e.hom).obj P := by rw [Subobject.mk_arrow]
  rw [← hm]
  exact Subobject.mk_factors_self (P.arrow ≫ e.hom)

/-- 原始 `E∞` 环境中的 `SSData` 到未截断复形数据的同构态射。 -/
noncomputable def unboundedSSDataForward
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω') :
    SSDataMorphism (ℤ × ℤ) (unboundedExtensionSSData cm t)
      (unboundedComplexSSDataFamily cm t) where
  φ := fun ⟨s, k⟩ => (unboundedExtensionVComplexIso cm t s k).hom
  preserves_Z := by
    rintro ⟨s, k⟩ r
    let e := unboundedExtensionVComplexIso cm t s k
    let P := (unboundedSSData cm t s k).Z r
    let Q := (unboundedComplexSSData cm t s k).Z r
    have hfac : Q.Factors (P.arrow ≫ e.hom) :=
      subobject_factors_of_mapIso_eq e P Q
        (unboundedExtensionSSData_map_Z cm t s k r)
    exact ⟨Q.factorThru (P.arrow ≫ e.hom) hfac, Q.factorThru_arrow _ hfac⟩
  preserves_B := by
    rintro ⟨s, k⟩ r
    let e := unboundedExtensionVComplexIso cm t s k
    let P := (unboundedSSData cm t s k).B r
    let Q := (unboundedComplexSSData cm t s k).B r
    have hfac : Q.Factors (P.arrow ≫ e.hom) :=
      subobject_factors_of_mapIso_eq e P Q
        (unboundedExtensionSSData_map_B cm t s k r)
    exact ⟨Q.factorThru (P.arrow ≫ e.hom) hfac, Q.factorThru_arrow _ hfac⟩

/-- 未截断复形数据到原始 `E∞` 环境中 `SSData` 的逆同构态射。 -/
noncomputable def unboundedSSDataBackward
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω') :
    SSDataMorphism (ℤ × ℤ) (unboundedComplexSSDataFamily cm t)
      (unboundedExtensionSSData cm t) where
  φ := fun ⟨s, k⟩ => (unboundedExtensionVComplexIso cm t s k).inv
  preserves_Z := by
    rintro ⟨s, k⟩ r
    let e := unboundedExtensionVComplexIso cm t s k
    have hback : (Subobject.mapIsoToOrderIso e.symm)
        ((unboundedComplexSSData cm t s k).Z r) =
          (unboundedSSData cm t s k).Z r := by
      rw [← unboundedExtensionSSData_map_Z cm t s k r]
      exact (Subobject.mapIsoToOrderIso e).symm_apply_apply _
    let P := (unboundedComplexSSData cm t s k).Z r
    let Q := (unboundedSSData cm t s k).Z r
    have hfac : Q.Factors (P.arrow ≫ e.inv) :=
      subobject_factors_of_mapIso_eq e.symm P Q hback
    exact ⟨Q.factorThru (P.arrow ≫ e.inv) hfac, Q.factorThru_arrow _ hfac⟩
  preserves_B := by
    rintro ⟨s, k⟩ r
    let e := unboundedExtensionVComplexIso cm t s k
    have hback : (Subobject.mapIsoToOrderIso e.symm)
        ((unboundedComplexSSData cm t s k).B r) =
          (unboundedSSData cm t s k).B r := by
      rw [← unboundedExtensionSSData_map_B cm t s k r]
      exact (Subobject.mapIsoToOrderIso e).symm_apply_apply _
    let P := (unboundedComplexSSData cm t s k).B r
    let Q := (unboundedSSData cm t s k).B r
    have hfac : Q.Factors (P.arrow ≫ e.inv) :=
      subobject_factors_of_mapIso_eq e.symm P Q hback
    exact ⟨Q.factorThru (P.arrow ≫ e.inv) hfac, Q.factorThru_arrow _ hfac⟩

/-- `SSData` 族的恒等态射。 -/
private noncomputable def ssDataMorphismId (D : ℤ × ℤ → SSData C) :
    SSDataMorphism (ℤ × ℤ) D D where
  φ := fun _ => 𝟙 _
  preserves_Z := fun k r => ⟨𝟙 _, by simp⟩
  preserves_B := fun k r => ⟨𝟙 _, by simp⟩

/-- 原始 `E∞` 环境中的有限页与未截断复形有限页的规范同构。 -/
noncomputable def unboundedExtensionPageIso
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω') (sk : ℤ × ℤ)
    (n : ℕ) :
    ((unboundedExtensionSSData cm t) sk).page n ≅
      ((unboundedComplexSSDataFamily cm t) sk).page n where
  hom := (unboundedSSDataForward cm t).pageMap sk n
  inv := (unboundedSSDataBackward cm t).pageMap sk n
  hom_inv_id := by
    rw [← SSDataMorphism.pageMap_eq_comp
      (unboundedSSDataForward cm t) (unboundedSSDataBackward cm t)
      (ssDataMorphismId (unboundedExtensionSSData cm t)) sk n (by
        rcases sk with ⟨s, k⟩
        exact (unboundedExtensionVComplexIso cm t s k).hom_inv_id.symm)]
    exact SSDataMorphism.pageMap_eq_id _ sk n rfl

  inv_hom_id := by
    rw [← SSDataMorphism.pageMap_eq_comp
      (unboundedSSDataBackward cm t) (unboundedSSDataForward cm t)
      (ssDataMorphismId (unboundedComplexSSDataFamily cm t)) sk n (by
        rcases sk with ⟨s, k⟩
        exact (unboundedExtensionVComplexIso cm t s k).inv_hom_id.symm)]
    exact SSDataMorphism.pageMap_eq_id _ sk n rfl

/-- 原始 `E∞` 环境中的任意页（包括顶页）与未截断复形数据的对应页同构。 -/
noncomputable def unboundedExtensionPageIsoWithTop
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω') (sk : ℤ × ℤ)
    (r : WithTop ℕ) :
    ((unboundedExtensionSSData cm t) sk).page r ≅
      ((unboundedComplexSSDataFamily cm t) sk).page r where
  hom := (unboundedSSDataForward cm t).pageMap sk r
  inv := (unboundedSSDataBackward cm t).pageMap sk r
  hom_inv_id := by
    rw [← SSDataMorphism.pageMap_eq_comp
      (unboundedSSDataForward cm t) (unboundedSSDataBackward cm t)
      (ssDataMorphismId (unboundedExtensionSSData cm t)) sk r (by
        rcases sk with ⟨s, k⟩
        exact (unboundedExtensionVComplexIso cm t s k).hom_inv_id.symm)]
    exact SSDataMorphism.pageMap_eq_id _ sk r rfl
  inv_hom_id := by
    rw [← SSDataMorphism.pageMap_eq_comp
      (unboundedSSDataBackward cm t) (unboundedSSDataForward cm t)
      (ssDataMorphismId (unboundedComplexSSDataFamily cm t)) sk r (by
        rcases sk with ⟨s, k⟩
        exact (unboundedExtensionVComplexIso cm t s k).inv_hom_id.symm)]
    exact SSDataMorphism.pageMap_eq_id _ sk r rfl

/-- 复形侧无界数据的第 `n` 页就是未截断两项复形的有限页。 -/
@[simp]
private theorem unboundedComplexSSData_page_nat
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω')
    (s k : ℤ) (n : ℕ) :
    (unboundedComplexSSData cm t s k).page (n : WithTop ℕ) =
      (unboundedUnderlyingComplex cm t).finitePage s k n :=
  rfl

/-- 同构前合成后的核沿该同构推前，等于原来的核。 -/
private theorem mapIso_kernelSubobject_comp {X Y Z : C}
    (e : X ≅ Y) (f : Y ⟶ Z) :
    (Subobject.map e.hom).obj (kernelSubobject (e.hom ≫ f)) =
      kernelSubobject f := by
  rw [← Subobject.mk_arrow (kernelSubobject (e.hom ≫ f)),
    Subobject.map_mk, ← Subobject.mk_arrow (kernelSubobject f)]
  exact Subobject.mk_eq_mk_of_comm _ _ (kernelSubobjectIsoComp e.hom f)
    (kernelSubobjectIsoComp_hom_arrow e.hom f)

/-- 一个态射的像沿目标同构推前，等于复合态射的像。 -/
private theorem mapIso_imageSubobject {X Y Z : C}
    (f : X ⟶ Y) (e : Y ≅ Z) :
    (Subobject.map e.hom).obj (imageSubobject f) =
      imageSubobject (f ≫ e.hom) := by
  rw [← Subobject.mk_arrow (imageSubobject f), Subobject.map_mk,
    ← Subobject.mk_arrow (imageSubobject (f ≫ e.hom))]
  exact Subobject.mk_eq_mk_of_comm _ _ (imageSubobjectCompIso f e.hom).symm
    (imageSubobjectCompIso_inv_arrow f e.hom)

/-- 共轭微分的核沿源页同构推前后恢复原核。 -/
private theorem mapIso_kernelSubobject_conjugate {X X' Y Y' : C}
    (eX : X ≅ X') (f : X' ⟶ Y') (eY : Y ≅ Y') :
    (Subobject.map eX.hom).obj
        (kernelSubobject (eX.hom ≫ f ≫ eY.inv)) =
      kernelSubobject f :=
  calc
    (Subobject.map eX.hom).obj
        (kernelSubobject (eX.hom ≫ f ≫ eY.inv)) =
        kernelSubobject (f ≫ eY.inv) :=
      mapIso_kernelSubobject_comp eX (f ≫ eY.inv)
    _ = kernelSubobject f := kernelSubobject_comp_mono f eY.inv

/-- 共轭微分的像沿目标页同构推前后恢复原像。 -/
private theorem mapIso_imageSubobject_conjugate {X X' Y Y' : C}
    (eX : X ≅ X') (f : X' ⟶ Y') (eY : Y ≅ Y') :
    (Subobject.map eY.hom).obj
        (imageSubobject (eX.hom ≫ f ≫ eY.inv)) =
      imageSubobject f := by
  calc
    (Subobject.map eY.hom).obj
        (imageSubobject (eX.hom ≫ f ≫ eY.inv)) =
        (Subobject.map eY.hom).obj (imageSubobject (f ≫ eY.inv)) := by
      rw [imageSubobject_iso_comp eX.hom (f ≫ eY.inv)]
    _ = imageSubobject ((f ≫ eY.inv) ≫ eY.hom) :=
      mapIso_imageSubobject (f ≫ eY.inv) eY
    _ = imageSubobject f := by
      simpa only [Category.assoc, eY.inv_hom_id, Category.comp_id]

/-- 原始 `E∞` 环境与复形环境中循环子对象底层对象的规范同构。 -/
noncomputable def unboundedExtensionZIso
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω')
    (sk : ℤ × ℤ) (r : WithTop ℕ) :
    Subobject.underlying.obj ((unboundedExtensionSSData cm t sk).Z r) ≅
      Subobject.underlying.obj ((unboundedComplexSSDataFamily cm t sk).Z r) where
  hom := (unboundedSSDataForward cm t).preserves_Z sk r |>.choose
  inv := (unboundedSSDataBackward cm t).preserves_Z sk r |>.choose
  hom_inv_id := by
    apply (cancel_mono ((unboundedExtensionSSData cm t sk).Z r).arrow).1
    simp only [Category.assoc, Category.id_comp]
    rw [(unboundedSSDataBackward cm t).preserves_Z sk r |>.choose_spec]
    rw [← Category.assoc,
      (unboundedSSDataForward cm t).preserves_Z sk r |>.choose_spec]
    rcases sk with ⟨s, k⟩
    have hφ : (unboundedSSDataForward cm t).φ (s, k) ≫
        (unboundedSSDataBackward cm t).φ (s, k) =
          𝟙 ((unboundedExtensionSSData cm t (s, k)).V) := by
      change (unboundedExtensionVComplexIso cm t s k).hom ≫
        (unboundedExtensionVComplexIso cm t s k).inv = 𝟙 _
      exact (unboundedExtensionVComplexIso cm t s k).hom_inv_id
    rw [Category.assoc, hφ, Category.comp_id]
  inv_hom_id := by
    apply (cancel_mono ((unboundedComplexSSDataFamily cm t sk).Z r).arrow).1
    simp only [Category.assoc, Category.id_comp]
    rw [(unboundedSSDataForward cm t).preserves_Z sk r |>.choose_spec]
    rw [← Category.assoc,
      (unboundedSSDataBackward cm t).preserves_Z sk r |>.choose_spec]
    rcases sk with ⟨s, k⟩
    have hφ : (unboundedSSDataBackward cm t).φ (s, k) ≫
        (unboundedSSDataForward cm t).φ (s, k) =
          𝟙 ((unboundedComplexSSDataFamily cm t (s, k)).V) := by
      change (unboundedExtensionVComplexIso cm t s k).inv ≫
        (unboundedExtensionVComplexIso cm t s k).hom = 𝟙 _
      exact (unboundedExtensionVComplexIso cm t s k).inv_hom_id
    rw [Category.assoc, hφ, Category.comp_id]

/-- 循环层逆同构与环境对象中的子对象箭头相容。 -/
theorem unboundedExtensionZIso_inv_arrow
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω')
    (s k : ℤ) (r : WithTop ℕ) :
    (unboundedExtensionZIso cm t (s, k) r).inv ≫
        ((unboundedExtensionSSData cm t (s, k)).Z r).arrow =
      ((unboundedComplexSSDataFamily cm t (s, k)).Z r).arrow ≫
        (unboundedExtensionVComplexIso cm t s k).inv := by
  exact (unboundedSSDataBackward cm t).preserves_Z (s, k) r |>.choose_spec

/-- 循环层正向同构与环境对象中的子对象箭头相容。 -/
theorem unboundedExtensionZIso_hom_arrow
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω')
    (s k : ℤ) (r : WithTop ℕ) :
    (unboundedExtensionZIso cm t (s, k) r).hom ≫
        ((unboundedComplexSSDataFamily cm t (s, k)).Z r).arrow =
      ((unboundedExtensionSSData cm t (s, k)).Z r).arrow ≫
        (unboundedExtensionVComplexIso cm t s k).hom := by
  exact (unboundedSSDataForward cm t).preserves_Z (s, k) r |>.choose_spec

/-- 循环层逆同构与页投影相容。 -/
theorem unboundedExtensionZIso_inv_pageπ
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω')
    (s k : ℤ) (r : WithTop ℕ) :
    (unboundedExtensionZIso cm t (s, k) r).inv ≫
        (unboundedExtensionSSData cm t (s, k)).pageπ r =
      (unboundedComplexSSDataFamily cm t (s, k)).pageπ r ≫
        (unboundedExtensionPageIsoWithTop cm t (s, k) r).inv := by
  exact ((unboundedSSDataBackward cm t).pageπ_pageMap (s, k) r).symm

/-- 在有限页上，循环层逆同构与有限页同构的逆及页投影相容。 -/
theorem unboundedExtensionZIso_inv_pageπ_nat
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω')
    (s k : ℤ) (n : ℕ) :
    (unboundedExtensionZIso cm t (s, k) (n : WithTop ℕ)).inv ≫
        (unboundedExtensionSSData cm t (s, k)).pageπ (n : WithTop ℕ) =
      (unboundedComplexSSDataFamily cm t (s, k)).pageπ (n : WithTop ℕ) ≫
        (unboundedExtensionPageIso cm t (s, k) n).inv := by
  exact ((unboundedSSDataBackward cm t).pageπ_pageMap
    (s, k) (n : WithTop ℕ)).symm

/-- 原始 `E∞` 环境与复形环境中边缘子对象底层对象的规范同构。 -/
noncomputable def unboundedExtensionBIso
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω')
    (sk : ℤ × ℤ) (r : WithTop ℕ) :
    Subobject.underlying.obj ((unboundedExtensionSSData cm t sk).B r) ≅
      Subobject.underlying.obj ((unboundedComplexSSDataFamily cm t sk).B r) where
  hom := (unboundedSSDataForward cm t).preserves_B sk r |>.choose
  inv := (unboundedSSDataBackward cm t).preserves_B sk r |>.choose
  hom_inv_id := by
    apply (cancel_mono ((unboundedExtensionSSData cm t sk).B r).arrow).1
    simp only [Category.assoc, Category.id_comp]
    rw [(unboundedSSDataBackward cm t).preserves_B sk r |>.choose_spec]
    rw [← Category.assoc,
      (unboundedSSDataForward cm t).preserves_B sk r |>.choose_spec]
    rcases sk with ⟨s, k⟩
    have hφ : (unboundedSSDataForward cm t).φ (s, k) ≫
        (unboundedSSDataBackward cm t).φ (s, k) =
          𝟙 ((unboundedExtensionSSData cm t (s, k)).V) := by
      change (unboundedExtensionVComplexIso cm t s k).hom ≫
        (unboundedExtensionVComplexIso cm t s k).inv = 𝟙 _
      exact (unboundedExtensionVComplexIso cm t s k).hom_inv_id
    rw [Category.assoc, hφ, Category.comp_id]
  inv_hom_id := by
    apply (cancel_mono ((unboundedComplexSSDataFamily cm t sk).B r).arrow).1
    simp only [Category.assoc, Category.id_comp]
    rw [(unboundedSSDataForward cm t).preserves_B sk r |>.choose_spec]
    rw [← Category.assoc,
      (unboundedSSDataBackward cm t).preserves_B sk r |>.choose_spec]
    rcases sk with ⟨s, k⟩
    have hφ : (unboundedSSDataBackward cm t).φ (s, k) ≫
        (unboundedSSDataForward cm t).φ (s, k) =
          𝟙 ((unboundedComplexSSDataFamily cm t (s, k)).V) := by
      change (unboundedExtensionVComplexIso cm t s k).inv ≫
        (unboundedExtensionVComplexIso cm t s k).hom = 𝟙 _
      exact (unboundedExtensionVComplexIso cm t s k).inv_hom_id
    rw [Category.assoc, hφ, Category.comp_id]

/-- 边缘层正向同构与环境对象中的子对象箭头相容。 -/
theorem unboundedExtensionBIso_hom_arrow
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω')
    (s k : ℤ) (r : WithTop ℕ) :
    (unboundedExtensionBIso cm t (s, k) r).hom ≫
        ((unboundedComplexSSDataFamily cm t (s, k)).B r).arrow =
      ((unboundedExtensionSSData cm t (s, k)).B r).arrow ≫
        (unboundedExtensionVComplexIso cm t s k).hom := by
  exact (unboundedSSDataForward cm t).preserves_B (s, k) r |>.choose_spec

/-- 原始 `E∞` 环境中的边缘分解经环境同构送到复形侧边缘分解。 -/
theorem unboundedExtension_boundary_factors_forward
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω')
    (s k : ℤ) (r : WithTop ℕ) {T : C}
    {z : T ⟶ (unboundedExtensionSSData cm t (s, k)).V}
    (hz : ((unboundedExtensionSSData cm t (s, k)).B r).Factors z) :
    ((unboundedComplexSSDataFamily cm t (s, k)).B r).Factors
      (z ≫ (unboundedExtensionVComplexIso cm t s k).hom) := by
  obtain ⟨b, hb⟩ := (Subobject.factors_iff _ _).1 hz
  apply (Subobject.factors_iff _ _).2
  refine ⟨b ≫ (unboundedExtensionBIso cm t (s, k) r).hom, ?_⟩
  calc
    (b ≫ (unboundedExtensionBIso cm t (s, k) r).hom) ≫
        ((unboundedComplexSSDataFamily cm t (s, k)).B r).arrow =
      b ≫ ((unboundedExtensionBIso cm t (s, k) r).hom ≫
        ((unboundedComplexSSDataFamily cm t (s, k)).B r).arrow) :=
          Category.assoc _ _ _
    _ = b ≫ (((unboundedExtensionSSData cm t (s, k)).B r).arrow ≫
        (unboundedExtensionVComplexIso cm t s k).hom) := by
          rw [unboundedExtensionBIso_hom_arrow]
    _ = (b ≫ ((unboundedExtensionSSData cm t (s, k)).B r).arrow) ≫
        (unboundedExtensionVComplexIso cm t s k).hom :=
          (Category.assoc _ _ _).symm
    _ = z ≫ (unboundedExtensionVComplexIso cm t s k).hom := by
      exact congrArg
        (fun q => q ≫ (unboundedExtensionVComplexIso cm t s k).hom) hb

/-- `Z_{n+1}` 在第 `n` 页中的规范映射。 -/
private noncomputable def ssDataZSuccMap (D : SSData C) (n : ℕ) :
    Subobject.underlying.obj (D.Z ↑(n + 1)) ⟶ D.page ↑n :=
  Subobject.ofLE (D.Z ↑(n + 1)) (D.Z ↑n)
      (D.Z_anti (by exact_mod_cast Nat.le_succ n)) ≫
    D.pageπ ↑n

/-- `B_{n+1}` 在第 `n` 页中的规范映射。 -/
private noncomputable def ssDataBSuccMap (D : SSData C) (n : ℕ) :
    Subobject.underlying.obj (D.B ↑(n + 1)) ⟶ D.page ↑n :=
  Subobject.ofLE (D.B ↑(n + 1)) (D.Z ↑n)
      (le_trans (D.B_le_Z ↑(n + 1))
        (D.Z_anti (by exact_mod_cast Nat.le_succ n))) ≫
    D.pageπ ↑n

/-- 循环层到页的规范映射与无界页同构交换。 -/
private theorem unboundedExtensionZSuccMap_comm
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω')
    (sk : ℤ × ℤ) (n : ℕ) :
    ssDataZSuccMap (unboundedExtensionSSData cm t sk) n ≫
        (unboundedExtensionPageIso cm t sk n).hom =
      (unboundedExtensionZIso cm t sk ↑(n + 1)).hom ≫
        ssDataZSuccMap (unboundedComplexSSDataFamily cm t sk) n := by
  have hinc : Subobject.ofLE
        ((unboundedExtensionSSData cm t sk).Z ↑(n + 1))
        ((unboundedExtensionSSData cm t sk).Z ↑n)
        ((unboundedExtensionSSData cm t sk).Z_anti
          (by exact_mod_cast Nat.le_succ n)) ≫
        (unboundedExtensionZIso cm t sk ↑n).hom =
      (unboundedExtensionZIso cm t sk ↑(n + 1)).hom ≫
        Subobject.ofLE
          ((unboundedComplexSSDataFamily cm t sk).Z ↑(n + 1))
          ((unboundedComplexSSDataFamily cm t sk).Z ↑n)
          ((unboundedComplexSSDataFamily cm t sk).Z_anti
            (by exact_mod_cast Nat.le_succ n)) := by
    apply (cancel_mono
      ((unboundedComplexSSDataFamily cm t sk).Z ↑n).arrow).1
    dsimp only [unboundedExtensionZIso]
    simp only [Category.assoc, Subobject.ofLE_arrow,
      Subobject.ofLE_arrow_assoc]
    rw [(unboundedSSDataForward cm t).preserves_Z sk ↑n |>.choose_spec,
      ← Category.assoc,
      (unboundedSSDataForward cm t).preserves_Z sk ↑(n + 1) |>.choose_spec]
    rw [Subobject.ofLE_arrow]
  dsimp only [unboundedExtensionZIso] at hinc
  unfold ssDataZSuccMap unboundedExtensionPageIso
  dsimp only [unboundedExtensionZIso]
  rw [Category.assoc,
    (unboundedSSDataForward cm t).pageπ_pageMap sk ↑n]
  rw [← Category.assoc, hinc, Category.assoc]

/-- 边缘层到页的规范映射与无界页同构交换。 -/
private theorem unboundedExtensionBSuccMap_comm
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω')
    (sk : ℤ × ℤ) (n : ℕ) :
    ssDataBSuccMap (unboundedExtensionSSData cm t sk) n ≫
        (unboundedExtensionPageIso cm t sk n).hom =
      (unboundedExtensionBIso cm t sk ↑(n + 1)).hom ≫
        ssDataBSuccMap (unboundedComplexSSDataFamily cm t sk) n := by
  have hinc : Subobject.ofLE
        ((unboundedExtensionSSData cm t sk).B ↑(n + 1))
        ((unboundedExtensionSSData cm t sk).Z ↑n)
        (le_trans
          ((unboundedExtensionSSData cm t sk).B_le_Z ↑(n + 1))
          ((unboundedExtensionSSData cm t sk).Z_anti
            (by exact_mod_cast Nat.le_succ n))) ≫
        (unboundedExtensionZIso cm t sk ↑n).hom =
      (unboundedExtensionBIso cm t sk ↑(n + 1)).hom ≫
        Subobject.ofLE
          ((unboundedComplexSSDataFamily cm t sk).B ↑(n + 1))
          ((unboundedComplexSSDataFamily cm t sk).Z ↑n)
          (le_trans
            ((unboundedComplexSSDataFamily cm t sk).B_le_Z ↑(n + 1))
            ((unboundedComplexSSDataFamily cm t sk).Z_anti
              (by exact_mod_cast Nat.le_succ n))) := by
    apply (cancel_mono
      ((unboundedComplexSSDataFamily cm t sk).Z ↑n).arrow).1
    dsimp only [unboundedExtensionZIso, unboundedExtensionBIso]
    simp only [Category.assoc, Subobject.ofLE_arrow,
      Subobject.ofLE_arrow_assoc]
    rw [(unboundedSSDataForward cm t).preserves_Z sk ↑n |>.choose_spec,
      ← Category.assoc,
      (unboundedSSDataForward cm t).preserves_B sk ↑(n + 1) |>.choose_spec]
    rw [Subobject.ofLE_arrow]
  dsimp only [unboundedExtensionZIso, unboundedExtensionBIso] at hinc
  unfold ssDataBSuccMap unboundedExtensionPageIso
  dsimp only [unboundedExtensionBIso]
  rw [Category.assoc,
    (unboundedSSDataForward cm t).pageπ_pageMap sk ↑n]
  rw [← Category.assoc, hinc, Category.assoc]

/-- 未截断两项复形自身的有限页微分，使用复形侧的 `SSData` 页作为类型。 -/
private noncomputable def unboundedComplexDifferential
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω')
    (s k : ℤ) (n : ℕ) :
    ((unboundedComplexSSDataFamily cm t) (s, k)).page ↑n ⟶
      ((unboundedComplexSSDataFamily cm t) (s + ↑n, k - 1)).page ↑n :=
  (unboundedUnderlyingComplex cm t).finitePageDifferential s k n

/-- 未截断两项复形的有限页微分平方为零。 -/
private theorem unboundedComplexDifferential_comp
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω')
    (s k : ℤ) (n : ℕ) :
    unboundedComplexDifferential cm t s k n ≫
      unboundedComplexDifferential cm t (s + ↑n) (k - 1) n = 0 := by
  change (unboundedUnderlyingComplex cm t).finitePageDifferential s k n ≫
    (unboundedUnderlyingComplex cm t).finitePageDifferential
      (s + ↑n) (k - 1) n = 0
  exact (unboundedUnderlyingComplex cm t).finitePageDifferential_comp s k n

/-- 无界扩张在第 `n` 页的微分。
它先由原始 `E∞` 环境中的页搬到未截断两项复形的有限页，
应用有限页核心微分，再搬回目标页。 -/
noncomputable def unboundedExtensionDifferential
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω')
    (s k : ℤ) (n : ℕ) :
    ((unboundedExtensionSSData cm t) (s, k)).page n ⟶
      ((unboundedExtensionSSData cm t) (s + ↑n, k - 1)).page n :=
  (unboundedExtensionPageIso cm t (s, k) n).hom ≫
    unboundedComplexDifferential cm t s k n ≫
    (unboundedExtensionPageIso cm t (s + ↑n, k - 1) n).inv

/-- 无界扩张的有限页微分平方为零。 -/
theorem unboundedExtensionDifferential_comp
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω')
    (s k : ℤ) (n : ℕ) :
    unboundedExtensionDifferential cm t s k n ≫
      unboundedExtensionDifferential cm t (s + ↑n) (k - 1) n = 0 := by
  simp only [unboundedExtensionDifferential, Category.assoc,
    Iso.inv_hom_id_assoc]
  rw [← Category.assoc
      (unboundedComplexDifferential cm t s k n),
    unboundedComplexDifferential_comp cm t s k n,
    zero_comp, comp_zero]

/-- 未截断复形有限页微分的核由下一循环层给出。 -/
theorem unboundedFiniteDifferential_Z_succ
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω')
    (s k : ℤ) (n : ℕ) :
    kernelSubobject
        ((unboundedUnderlyingComplex cm t).finitePageDifferential s k n) =
      imageSubobject (Subobject.ofLE
        ((unboundedUnderlyingComplex cm t).cycleSubobject s k ↑(n + 1))
        ((unboundedUnderlyingComplex cm t).cycleSubobject s k ↑n)
        ((unboundedUnderlyingComplex cm t).cycleSubobject_nat_anti
          s k (Nat.le_succ n)) ≫
        (unboundedUnderlyingComplex cm t).finitePageπ s k n) := by
  apply le_antisymm
  · exact pageDifferential_Z_succ_le
      (unboundedUnderlyingComplex cm t) s k n
  · exact pageDifferential_Z_succ_ge
      (unboundedUnderlyingComplex cm t) s k n

/-- 未截断复形有限页微分的像由下一边缘层给出。 -/
theorem unboundedFiniteDifferential_B_succ
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω')
    (s k : ℤ) (n : ℕ) :
    imageSubobject
        ((unboundedUnderlyingComplex cm t).finitePageDifferential s k n) =
      imageSubobject (Subobject.ofLE
        ((unboundedUnderlyingComplex cm t).boundarySubobject
          (s + ↑n) (k - 1) ↑(n + 1))
        ((unboundedUnderlyingComplex cm t).cycleSubobject
          (s + ↑n) (k - 1) ↑n)
        (le_trans
          ((unboundedUnderlyingComplex cm t).B_le_Z_aux
            (s + ↑n) (k - 1) (n + 1))
          ((unboundedUnderlyingComplex cm t).cycleSubobject_nat_anti
            (s + ↑n) (k - 1) (Nat.le_succ n))) ≫
        (unboundedUnderlyingComplex cm t).finitePageπ
          (s + ↑n) (k - 1) n) :=
  (unboundedUnderlyingComplex cm t).finitePageDifferential_B_succ s k n

/-- 复形侧无界有限页微分的核是下一循环层在当前页中的像。 -/
private theorem unboundedComplexDifferential_Z_succ
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω')
    (s k : ℤ) (n : ℕ) :
    kernelSubobject (unboundedComplexDifferential cm t s k n) =
      imageSubobject
        (ssDataZSuccMap (unboundedComplexSSDataFamily cm t (s, k)) n) := by
  change kernelSubobject
      ((unboundedUnderlyingComplex cm t).finitePageDifferential s k n) =
    imageSubobject (Subobject.ofLE
      ((unboundedUnderlyingComplex cm t).cycleSubobject s k ↑(n + 1))
      ((unboundedUnderlyingComplex cm t).cycleSubobject s k ↑n)
      ((unboundedUnderlyingComplex cm t).cycleSubobject_nat_anti
        s k (Nat.le_succ n)) ≫
      (unboundedUnderlyingComplex cm t).finitePageπ s k n)
  exact unboundedFiniteDifferential_Z_succ cm t s k n

/-- 复形侧无界有限页微分的像是下一边缘层在当前页中的像。 -/
private theorem unboundedComplexDifferential_B_succ
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω')
    (s k : ℤ) (n : ℕ) :
    imageSubobject (unboundedComplexDifferential cm t s k n) =
      imageSubobject (ssDataBSuccMap
        (unboundedComplexSSDataFamily cm t (s + ↑n, k - 1)) n) := by
  change imageSubobject
      ((unboundedUnderlyingComplex cm t).finitePageDifferential s k n) =
    imageSubobject (Subobject.ofLE
      ((unboundedUnderlyingComplex cm t).boundarySubobject
        (s + ↑n) (k - 1) ↑(n + 1))
      ((unboundedUnderlyingComplex cm t).cycleSubobject
        (s + ↑n) (k - 1) ↑n)
      (le_trans
        ((unboundedUnderlyingComplex cm t).B_le_Z_aux
          (s + ↑n) (k - 1) (n + 1))
        ((unboundedUnderlyingComplex cm t).cycleSubobject_nat_anti
          (s + ↑n) (k - 1) (Nat.le_succ n))) ≫
      (unboundedUnderlyingComplex cm t).finitePageπ
        (s + ↑n) (k - 1) n)
  exact unboundedFiniteDifferential_B_succ cm t s k n

/-- 无界扩张微分的核是原始 `E∞` 环境中下一循环层在当前页中的像。 -/
theorem unboundedExtensionDifferential_Z_succ
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω')
    (s k : ℤ) (n : ℕ) :
    kernelSubobject (unboundedExtensionDifferential cm t s k n) =
      imageSubobject
        (ssDataZSuccMap (unboundedExtensionSSData cm t (s, k)) n) := by
  let eS := unboundedExtensionPageIso cm t (s, k) n
  let eT := unboundedExtensionPageIso cm t (s + ↑n, k - 1) n
  let dC := unboundedComplexDifferential cm t s k n
  apply (Subobject.map_obj_injective eS.hom)
  calc
    (Subobject.map eS.hom).obj
        (kernelSubobject (unboundedExtensionDifferential cm t s k n)) =
        kernelSubobject dC := by
      simpa only [eS, eT, dC, unboundedExtensionDifferential] using
        mapIso_kernelSubobject_conjugate eS dC eT
    _ = imageSubobject
        (ssDataZSuccMap (unboundedComplexSSDataFamily cm t (s, k)) n) :=
      unboundedComplexDifferential_Z_succ cm t s k n
    _ = (Subobject.map eS.hom).obj
        (imageSubobject
          (ssDataZSuccMap (unboundedExtensionSSData cm t (s, k)) n)) := by
      symm
      rw [mapIso_imageSubobject]
      simpa only [eS,
        unboundedExtensionZSuccMap_comm cm t (s, k) n] using
        imageSubobject_iso_comp
          (unboundedExtensionZIso cm t (s, k) ↑(n + 1)).hom
          (ssDataZSuccMap (unboundedComplexSSDataFamily cm t (s, k)) n)

/-- 无界扩张微分的像是原始 `E∞` 环境中下一边缘层在当前页中的像。 -/
theorem unboundedExtensionDifferential_B_succ
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω')
    (s k : ℤ) (n : ℕ) :
    imageSubobject (unboundedExtensionDifferential cm t s k n) =
      imageSubobject (ssDataBSuccMap
        (unboundedExtensionSSData cm t (s + ↑n, k - 1)) n) := by
  let eS := unboundedExtensionPageIso cm t (s, k) n
  let eT := unboundedExtensionPageIso cm t (s + ↑n, k - 1) n
  let dC := unboundedComplexDifferential cm t s k n
  apply (Subobject.map_obj_injective eT.hom)
  calc
    (Subobject.map eT.hom).obj
        (imageSubobject (unboundedExtensionDifferential cm t s k n)) =
        imageSubobject dC := by
      simpa only [eS, eT, dC, unboundedExtensionDifferential] using
        mapIso_imageSubobject_conjugate eS dC eT
    _ = imageSubobject (ssDataBSuccMap
        (unboundedComplexSSDataFamily cm t (s + ↑n, k - 1)) n) :=
      unboundedComplexDifferential_B_succ cm t s k n
    _ = (Subobject.map eT.hom).obj
        (imageSubobject (ssDataBSuccMap
          (unboundedExtensionSSData cm t (s + ↑n, k - 1)) n)) := by
      symm
      rw [mapIso_imageSubobject]
      simpa only [eT, unboundedExtensionBSuccMap_comm cm t
        (s + ↑n, k - 1) n] using
        imageSubobject_iso_comp
          (unboundedExtensionBIso cm t (s + ↑n, k - 1) ↑(n + 1)).hom
          (ssDataBSuccMap
            (unboundedComplexSSDataFamily cm t (s + ↑n, k - 1)) n)

/-- 由原始 `E∞` 环境中的无界数据组成预谱序列。 -/
private noncomputable def unboundedExtensionPreSS
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω') :
    PreSS C (ℤ × ℤ) where
  r₀ := 0
  ssData := unboundedExtensionSSData cm t
  diffDeg := fun r => (r, -1)
  d := fun r ⟨s, k⟩ =>
    if hr : 0 ≤ r then
      eqToHom (by simp only [sub_zero]) ≫
        unboundedExtensionDifferential cm t s k r.toNat ≫
        eqToHom (by
          simp only [sub_zero, Int.toNat_of_nonneg hr]
          congr 2 <;> omega)
    else 0

/-- 无界预谱序列在自然数页上的微分就是单独定义的无界微分。 -/
private theorem unboundedExtensionPreSS_d_nat
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω')
    (s k : ℤ) (n : ℕ) :
    (unboundedExtensionPreSS cm t).d (n : ℤ) (s, k) =
      unboundedExtensionDifferential cm t s k n := by
  dsimp only [unboundedExtensionPreSS]
  simp only [Int.toNat_natCast, sub_zero,
    dif_pos (Int.natCast_nonneg n), eqToHom_refl,
    Category.id_comp, Category.comp_id]

/-- 无界预谱序列在负页上的微分为零。 -/
private theorem unboundedExtensionPreSS_d_neg
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω')
    (r : ℤ) (hr : ¬ 0 ≤ r) (sk : ℤ × ℤ) :
    (unboundedExtensionPreSS cm t).d r sk = 0 := by
  rcases sk with ⟨s, k⟩
  dsimp only [unboundedExtensionPreSS]
  rw [dif_neg hr]

/-- 无界预谱序列的微分平方为零。 -/
private theorem unboundedExtensionPreSS_d_comp_d
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω')
    (r : ℤ) (sk : ℤ × ℤ) :
    (unboundedExtensionPreSS cm t).d r sk ≫
      (unboundedExtensionPreSS cm t).d r
        (sk + (unboundedExtensionPreSS cm t).diffDeg r) = 0 := by
  rcases sk with ⟨s, k⟩
  by_cases hr : 0 ≤ r
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hr
    rw [unboundedExtensionPreSS_d_nat cm t s k n]
    change unboundedExtensionDifferential cm t s k n ≫
      (unboundedExtensionPreSS cm t).d (↑n) (s + ↑n, k - 1) = 0
    rw [unboundedExtensionPreSS_d_nat cm t (s + ↑n) (k - 1) n]
    exact unboundedExtensionDifferential_comp cm t s k n
  · rw [unboundedExtensionPreSS_d_neg cm t r hr]
    exact zero_comp

/-- 原始 `E∞` 环境中的独立微分与循环塔满足谱序列核公理。 -/
private theorem unboundedExtensionPreSS_Z_succ
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω')
    (r : ℤ) (sk : ℤ × ℤ) (hr : 0 ≤ r) :
    let n := (r - (unboundedExtensionPreSS cm t).r₀).toNat
    kernelSubobject ((unboundedExtensionPreSS cm t).d r sk) =
      imageSubobject (Subobject.ofLE
        (((unboundedExtensionPreSS cm t).ssData sk).Z ↑(n + 1))
        (((unboundedExtensionPreSS cm t).ssData sk).Z ↑n)
        (((unboundedExtensionPreSS cm t).ssData sk).Z_anti
          (by exact_mod_cast Nat.le_succ n)) ≫
        ((unboundedExtensionPreSS cm t).ssData sk).pageπ ↑n) := by
  rcases sk with ⟨s, k⟩
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hr
  simp only [unboundedExtensionPreSS_d_nat, Int.toNat_natCast, sub_zero]
  change kernelSubobject (unboundedExtensionDifferential cm t s k n) =
    imageSubobject
      (ssDataZSuccMap (unboundedExtensionSSData cm t (s, k)) n)
  exact unboundedExtensionDifferential_Z_succ cm t s k n

/-- 原始 `E∞` 环境中的独立微分与边缘塔满足谱序列像公理。 -/
private theorem unboundedExtensionPreSS_B_succ
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω')
    (r : ℤ) (sk : ℤ × ℤ) (hr : 0 ≤ r) :
    let n := (r - (unboundedExtensionPreSS cm t).r₀).toNat
    imageSubobject ((unboundedExtensionPreSS cm t).d r sk) =
      imageSubobject (Subobject.ofLE
        (((unboundedExtensionPreSS cm t).ssData
          (sk + (unboundedExtensionPreSS cm t).diffDeg r)).B ↑(n + 1))
        (((unboundedExtensionPreSS cm t).ssData
          (sk + (unboundedExtensionPreSS cm t).diffDeg r)).Z ↑n)
        (le_trans
          (((unboundedExtensionPreSS cm t).ssData
            (sk + (unboundedExtensionPreSS cm t).diffDeg r)).B_le_Z ↑(n + 1))
          (((unboundedExtensionPreSS cm t).ssData
            (sk + (unboundedExtensionPreSS cm t).diffDeg r)).Z_anti
              (by exact_mod_cast Nat.le_succ n))) ≫
        ((unboundedExtensionPreSS cm t).ssData
          (sk + (unboundedExtensionPreSS cm t).diffDeg r)).pageπ ↑n) := by
  rcases sk with ⟨s, k⟩
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hr
  simp only [unboundedExtensionPreSS_d_nat, Int.toNat_natCast, sub_zero]
  change imageSubobject (unboundedExtensionDifferential cm t s k n) =
    imageSubobject (ssDataBSuccMap
      (unboundedExtensionSSData cm t (s + ↑n, k - 1)) n)
  exact unboundedExtensionDifferential_B_succ cm t s k n

/-- 由原始 `E∞` 环境中的微分和 `Z/B` 塔组装出的无界扩张谱序列。 -/
private noncomputable def unboundedExtensionSpectralSequenceCore
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω') :
    SpectralSequence C (ℤ × ℤ) :=
  SpectralSequence.ofPreSS (unboundedExtensionPreSS cm t)
    (unboundedExtensionPreSS_d_comp_d cm t)
    (unboundedExtensionPreSS_Z_succ cm t)
    (unboundedExtensionPreSS_B_succ cm t)

/-- The extension spectral sequence constructed directly from the finite
cycle and boundary towers in the original `E∞` objects.  Its construction
does not require a boundedness hypothesis. -/
noncomputable def ExtensionSpectralSequence
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω') :
    SpectralSequence C (ℤ × ℤ) :=
  unboundedExtensionSpectralSequenceCore cm t

@[simp]
theorem ExtensionSpectralSequence_r₀
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω') :
    (ExtensionSpectralSequence cm t).r₀ = 0 :=
  rfl

@[simp]
theorem ExtensionSpectralSequence_diffDeg
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω') (r : ℤ) :
    (ExtensionSpectralSequence cm t).diffDeg r = (r, -1) :=
  rfl

/-- 无界扩张谱序列使用原始 `E∞` 环境中的 `SSData`。 -/
@[simp]
theorem ExtensionSpectralSequence_ssData
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω') (sk : ℤ × ℤ) :
    (ExtensionSpectralSequence cm t).ssData sk =
      unboundedExtensionSSData cm t sk :=
  rfl

/-- 无界扩张谱序列在自然数页上的微分就是独立构造的有限页微分。 -/
theorem ExtensionSpectralSequence_d_nat
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω')
    (s k : ℤ) (n : ℕ) :
    (ExtensionSpectralSequence cm t).d (n : ℤ) (s, k) =
      unboundedExtensionDifferential cm t s k n := by
  change (unboundedExtensionPreSS cm t).d (n : ℤ) (s, k) = _
  exact unboundedExtensionPreSS_d_nat cm t s k n

/-- 无界扩张谱序列的负页微分按构造为零。 -/
theorem ExtensionSpectralSequence_d_neg
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω')
    (r : ℤ) (hr : r < 0) (sk : ℤ × ℤ) :
    (ExtensionSpectralSequence cm t).d r sk = 0 := by
  change (unboundedExtensionPreSS cm t).d r sk = 0
  exact unboundedExtensionPreSS_d_neg cm t r (by omega) sk

end SubobjectLimits

/-! ### Section 1: Truncated extension spectral sequence -/

noncomputable def truncatedUnderlyingComplex
    (cm : ConvergenceMorphism conv₁ conv₂) (s₀ : ℤ) (t : ω') :
    FilteredComplex C :=
  underlyingComplex
    (fun k' => cm.truncatedAMap s₀ k')
    (fun s k' => cm.truncatedFiltrationCompat s₀ s k')
    t

noncomputable def truncatedUnderlyingComplex_isBounded
    (cm : ConvergenceMorphism conv₁ conv₂)
    (hbb₁ : F₁.IsBoundedBelow) (hbb₂ : F₂.IsBoundedBelow)
    (s₀ : ℤ) (t : ω') :
    (truncatedUnderlyingComplex cm s₀ t).IsBounded :=
  underlyingComplexBounded
    (fun k' => cm.truncatedAMap s₀ k')
    (fun s k' => cm.truncatedFiltrationCompat s₀ s k')
    t
    (F₁.truncatedFiltration_isBounded hbb₁ s₀)
    (F₂.truncatedFiltration_isBounded hbb₂ s₀)

noncomputable def truncatedESS
    (cm : ConvergenceMorphism conv₁ conv₂)
    (hbb₁ : F₁.IsBoundedBelow) (hbb₂ : F₂.IsBoundedBelow)
    (s₀ : ℤ) (t : ω') :
    SpectralSequence C (ℤ × ℤ) :=
  (truncatedUnderlyingComplex cm s₀ t).toSpectralSequence
    (truncatedUnderlyingComplex_isBounded cm hbb₁ hbb₂ s₀ t)

/-- 未截断两项过滤复形到第 `s₀` 个截断复形的规范投影态射。 -/
noncomputable def unboundedUnderlyingComplexProjection
    (cm : ConvergenceMorphism conv₁ conv₂) (s₀ : ℤ) (t : ω') :
    FilteredComplexMorphism (unboundedUnderlyingComplex cm t)
      (truncatedUnderlyingComplex cm s₀ t) :=
  underlyingComplexMorphism
    (fun k' => cm.aMap k')
    (fun s k' => cm.filtration_compat s k')
    (fun k' => cm.truncatedAMap s₀ k')
    (fun s k' => cm.truncatedFiltrationCompat s₀ s k')
    (fun k' => F₁.truncationProj s₀ k')
    (fun k' => F₂.truncationProj s₀ k')
    (fun k' => by
      simp only [Filtration.truncationProj,
        ConvergenceMorphism.truncatedAMap, cokernel.π_desc])
    (fun s k' => ⟨F₁.toTruncatedFiltration s₀ s k',
      F₁.toTruncatedFiltration_arrow s₀ s k'⟩)
    (fun s k' => ⟨F₂.toTruncatedFiltration s₀ s k',
      F₂.toTruncatedFiltration_arrow s₀ s k'⟩) t

/-- 未截断到截断投影在次数 `1` 的对象分量就是第一个过滤的商投影。 -/
private theorem unboundedUCProjection_f_one
    (cm : ConvergenceMorphism conv₁ conv₂) (s₀ : ℤ) (t : ω') :
    (unboundedUnderlyingComplexProjection cm s₀ t).f 1 =
      F₁.truncationProj s₀ t := by
  simp [unboundedUnderlyingComplexProjection, underlyingComplexMorphism,
    unboundedUnderlyingComplex, truncatedUnderlyingComplex,
    underlyingComplex, twoTermObj]

/-- 未截断到截断投影在次数 `0` 的对象分量就是第二个过滤的商投影。 -/
private theorem unboundedUCProjection_f_zero
    (cm : ConvergenceMorphism conv₁ conv₂) (s₀ : ℤ) (t : ω') :
    (unboundedUnderlyingComplexProjection cm s₀ t).f 0 =
      F₂.truncationProj s₀ t := by
  simp [unboundedUnderlyingComplexProjection, underlyingComplexMorphism,
    unboundedUnderlyingComplex, truncatedUnderlyingComplex,
    underlyingComplex, twoTermObj]

/-- 次数 `1` 的保过滤提升就是第一个过滤的规范截断满射。 -/
private theorem unboundedUCProjection_filtCompat_one
    (cm : ConvergenceMorphism conv₁ conv₂) (s₀ : ℤ) (t : ω') (s : ℤ) :
    ((unboundedUnderlyingComplexProjection cm s₀ t).filt_compat s 1).choose =
      F₁.toTruncatedFiltration s₀ s t := by
  apply (cancel_mono
    ((truncatedUnderlyingComplex cm s₀ t).fil s 1).arrow).1
  rw [((unboundedUnderlyingComplexProjection cm s₀ t).filt_compat s 1).choose_spec]
  simpa [unboundedUCProjection_f_one, unboundedUnderlyingComplex,
    truncatedUnderlyingComplex, underlyingComplex, twoTermFil, twoTermObj] using
    (F₁.toTruncatedFiltration_arrow s₀ s t).symm

/-- 次数 `0` 的保过滤提升就是第二个过滤的规范截断满射。 -/
private theorem unboundedUCProjection_filtCompat_zero
    (cm : ConvergenceMorphism conv₁ conv₂) (s₀ : ℤ) (t : ω') (s : ℤ) :
    ((unboundedUnderlyingComplexProjection cm s₀ t).filt_compat s 0).choose =
      F₂.toTruncatedFiltration s₀ s t := by
  apply (cancel_mono
    ((truncatedUnderlyingComplex cm s₀ t).fil s 0).arrow).1
  rw [((unboundedUnderlyingComplexProjection cm s₀ t).filt_compat s 0).choose_spec]
  simpa [unboundedUCProjection_f_zero, unboundedUnderlyingComplex,
    truncatedUnderlyingComplex, underlyingComplex, twoTermFil, twoTermObj] using
    (F₂.toTruncatedFiltration_arrow s₀ s t).symm

/-! ### Section 2: Inverse system structure -/

/-- The truncation transition preserves the truncated filtration of F₁. -/
private theorem truncationTransition_fil_compat₁
    {s₀ s₁ : ℤ} (hle : s₀ ≤ s₁) (s' : ℤ) (k' : ω') :
    ∃ (φ : Subobject.underlying.obj ((F₁.truncatedFiltration s₁).F s' k') ⟶
           Subobject.underlying.obj ((F₁.truncatedFiltration s₀).F s' k')),
      φ ≫ ((F₁.truncatedFiltration s₀).F s' k').arrow =
        ((F₁.truncatedFiltration s₁).F s' k').arrow ≫ F₁.truncationTransition hle k' := by
  have sq_comm : 𝟙 _ ≫ ((F₁.F s' k').arrow ≫ F₁.truncationProj s₀ k') =
      ((F₁.F s' k').arrow ≫ F₁.truncationProj s₁ k') ≫ F₁.truncationTransition hle k' := by
    simp only [Category.id_comp, Category.assoc, F₁.truncationProj_transition hle k']
  exact ⟨imageSubobjectMap (Arrow.homMk (𝟙 _) (F₁.truncationTransition hle k') sq_comm),
         imageSubobjectMap_arrow _⟩

/-- The truncation transition preserves the truncated filtration of F₂. -/
private theorem truncationTransition_fil_compat₂
    {s₀ s₁ : ℤ} (hle : s₀ ≤ s₁) (s' : ℤ) (k' : ω') :
    ∃ (φ : Subobject.underlying.obj ((F₂.truncatedFiltration s₁).F s' k') ⟶
           Subobject.underlying.obj ((F₂.truncatedFiltration s₀).F s' k')),
      φ ≫ ((F₂.truncatedFiltration s₀).F s' k').arrow =
        ((F₂.truncatedFiltration s₁).F s' k').arrow ≫ F₂.truncationTransition hle k' := by
  have sq_comm : 𝟙 _ ≫ ((F₂.F s' k').arrow ≫ F₂.truncationProj s₀ k') =
      ((F₂.F s' k').arrow ≫ F₂.truncationProj s₁ k') ≫ F₂.truncationTransition hle k' := by
    simp only [Category.id_comp, Category.assoc, F₂.truncationProj_transition hle k']
  exact ⟨imageSubobjectMap (Arrow.homMk (𝟙 _) (F₂.truncationTransition hle k') sq_comm),
         imageSubobjectMap_arrow _⟩

/-- 原过滤到两个截断关联分次的映射与截断转移相容。 -/
private theorem truncatedAssociatedGraded_transition₁
    {s₀ s₁ : ℤ} (h : s₀ ≤ s₁) (s : ℤ) (k : ω') :
    F₁.toTruncatedAssociatedGraded s₁ s k ≫
        Filtration.inducedAssocGradedMap
          (fun k' => F₁.truncationTransition h k')
          (fun s' k' => truncationTransition_fil_compat₁ h s' k') s k =
      F₁.toTruncatedAssociatedGraded s₀ s k := by
  haveI : Epi (F₁.toAssociatedGraded s k) := by
    unfold Filtration.toAssociatedGraded
    infer_instance
  have hmap : F₁.toTruncatedFiltration s₁ s k ≫
        (truncationTransition_fil_compat₁ (F₁ := F₁) h s k).choose =
      F₁.toTruncatedFiltration s₀ s k := by
    apply (cancel_mono
      ((F₁.truncatedFiltration s₀).F s k).arrow).1
    simp only [Category.assoc, Filtration.toTruncatedFiltration_arrow]
    rw [(truncationTransition_fil_compat₁ (F₁ := F₁) h s k).choose_spec]
    rw [← Category.assoc, F₁.toTruncatedFiltration_arrow,
      Category.assoc, F₁.truncationProj_transition h k]
  apply (cancel_epi (F₁.toAssociatedGraded s k)).1
  unfold Filtration.toTruncatedAssociatedGraded
    Filtration.toAssociatedGraded Filtration.inducedAssocGradedMap cokernel.map
  rw [← Category.assoc, cokernel.π_desc, cokernel.π_desc]
  rw [Category.assoc, cokernel.π_desc]
  rw [← Category.assoc, hmap]

/-- 第二个过滤的截断关联分次转移也与原过滤的投影相容。 -/
private theorem truncatedAssociatedGraded_transition₂
    {s₀ s₁ : ℤ} (h : s₀ ≤ s₁) (s : ℤ) (k : ω') :
    F₂.toTruncatedAssociatedGraded s₁ s k ≫
        Filtration.inducedAssocGradedMap
          (fun k' => F₂.truncationTransition h k')
          (fun s' k' => truncationTransition_fil_compat₂ h s' k') s k =
      F₂.toTruncatedAssociatedGraded s₀ s k := by
  haveI : Epi (F₂.toAssociatedGraded s k) := by
    unfold Filtration.toAssociatedGraded
    infer_instance
  have hmap : F₂.toTruncatedFiltration s₁ s k ≫
        (truncationTransition_fil_compat₂ (F₂ := F₂) h s k).choose =
      F₂.toTruncatedFiltration s₀ s k := by
    apply (cancel_mono
      ((F₂.truncatedFiltration s₀).F s k).arrow).1
    simp only [Category.assoc, Filtration.toTruncatedFiltration_arrow]
    rw [(truncationTransition_fil_compat₂ (F₂ := F₂) h s k).choose_spec]
    rw [← Category.assoc, F₂.toTruncatedFiltration_arrow,
      Category.assoc, F₂.truncationProj_transition h k]
  apply (cancel_epi (F₂.toAssociatedGraded s k)).1
  unfold Filtration.toTruncatedAssociatedGraded
    Filtration.toAssociatedGraded Filtration.inducedAssocGradedMap cokernel.map
  rw [← Category.assoc, cokernel.π_desc, cokernel.π_desc]
  rw [Category.assoc, cokernel.π_desc]
  rw [← Category.assoc, hmap]

/-- 当关联分次次数不超过较浅截断层时，第一个过滤的截断转移是同构。 -/
private noncomputable def truncatedAssociatedGradedTransitionIso₁
    {s₀ s₁ : ℤ} (h : s₀ ≤ s₁) (s : ℤ) (k : ω') (hs : s ≤ s₀) :
    (F₁.truncatedFiltration s₁).associatedGraded s k ≅
      (F₁.truncatedFiltration s₀).associatedGraded s k :=
  (F₁.truncatedAssociatedGradedIso s₁ s k (le_trans hs h)).symm ≪≫
    F₁.truncatedAssociatedGradedIso s₀ s k hs

/-- 上述同构的正向映射就是由截断转移诱导的关联分次映射。 -/
private theorem truncatedAssociatedGradedTransitionIso₁_hom
    {s₀ s₁ : ℤ} (h : s₀ ≤ s₁) (s : ℤ) (k : ω') (hs : s ≤ s₀) :
    (truncatedAssociatedGradedTransitionIso₁ (F₁ := F₁) h s k hs).hom =
      Filtration.inducedAssocGradedMap
        (fun k' => F₁.truncationTransition h k')
        (fun s' k' => truncationTransition_fil_compat₁ h s' k') s k := by
  let e₁ := F₁.truncatedAssociatedGradedIso s₁ s k (le_trans hs h)
  let e₀ := F₁.truncatedAssociatedGradedIso s₀ s k hs
  change e₁.inv ≫ e₀.hom = _
  apply (cancel_epi e₁.hom).1
  rw [← Category.assoc, e₁.hom_inv_id, Category.id_comp]
  exact (truncatedAssociatedGraded_transition₁ (F₁ := F₁) h s k).symm

/-- 当关联分次次数不超过较浅截断层时，第二个过滤的截断转移是同构。 -/
private noncomputable def truncatedAssociatedGradedTransitionIso₂
    {s₀ s₁ : ℤ} (h : s₀ ≤ s₁) (s : ℤ) (k : ω') (hs : s ≤ s₀) :
    (F₂.truncatedFiltration s₁).associatedGraded s k ≅
      (F₂.truncatedFiltration s₀).associatedGraded s k :=
  (F₂.truncatedAssociatedGradedIso s₁ s k (le_trans hs h)).symm ≪≫
    F₂.truncatedAssociatedGradedIso s₀ s k hs

/-- 第二个过滤的同构也逐字等于转移所诱导的关联分次映射。 -/
private theorem truncatedAssociatedGradedTransitionIso₂_hom
    {s₀ s₁ : ℤ} (h : s₀ ≤ s₁) (s : ℤ) (k : ω') (hs : s ≤ s₀) :
    (truncatedAssociatedGradedTransitionIso₂ (F₂ := F₂) h s k hs).hom =
      Filtration.inducedAssocGradedMap
        (fun k' => F₂.truncationTransition h k')
        (fun s' k' => truncationTransition_fil_compat₂ h s' k') s k := by
  let e₁ := F₂.truncatedAssociatedGradedIso s₁ s k (le_trans hs h)
  let e₀ := F₂.truncatedAssociatedGradedIso s₀ s k hs
  change e₁.inv ≫ e₀.hom = _
  apply (cancel_epi e₁.hom).1
  rw [← Category.assoc, e₁.hom_inv_id, Category.id_comp]
  exact (truncatedAssociatedGraded_transition₂ (F₂ := F₂) h s k).symm

/-- Naturality: truncatedAMap commutes with truncation transitions.
    F₁.truncationTransition ≫ cm.truncatedAMap s₀ = cm.truncatedAMap s₁ ≫ F₂.truncationTransition -/
private theorem truncatedAMap_naturality
    (cm : ConvergenceMorphism conv₁ conv₂)
    {s₀ s₁ : ℤ} (hle : s₀ ≤ s₁) (k' : ω') :
    F₁.truncationTransition hle k' ≫ cm.truncatedAMap s₀ k' =
      cm.truncatedAMap s₁ k' ≫ F₂.truncationTransition hle k' := by
  haveI : Epi (F₁.truncationProj s₁ k') := by
    unfold Filtration.truncationProj; infer_instance
  suffices key : F₁.truncationProj s₁ k' ≫ F₁.truncationTransition hle k' ≫
      cm.truncatedAMap s₀ k' =
      F₁.truncationProj s₁ k' ≫ cm.truncatedAMap s₁ k' ≫
      F₂.truncationTransition hle k' from (cancel_epi (F₁.truncationProj s₁ k')).mp key
  have lhs_eq : F₁.truncationProj s₁ k' ≫ F₁.truncationTransition hle k' ≫
      cm.truncatedAMap s₀ k' = cm.aMap k' ≫ F₂.truncationProj s₀ k' := by
    rw [← Category.assoc, F₁.truncationProj_transition hle k']
    simp [Filtration.truncationProj, ConvergenceMorphism.truncatedAMap, cokernel.π_desc]
  have rhs_eq : F₁.truncationProj s₁ k' ≫ cm.truncatedAMap s₁ k' ≫
      F₂.truncationTransition hle k' = cm.aMap k' ≫ F₂.truncationProj s₀ k' := by
    have h_proj : F₁.truncationProj s₁ k' ≫ cm.truncatedAMap s₁ k' =
        cm.aMap k' ≫ F₂.truncationProj s₁ k' := by
      simp [Filtration.truncationProj, ConvergenceMorphism.truncatedAMap, cokernel.π_desc]
    rw [← Category.assoc, h_proj, Category.assoc, F₂.truncationProj_transition hle k']
  rw [lhs_eq, rhs_eq]

/-- The assocGraded of the truncated underlying complex at k=1 equals
    the associatedGraded of the F₁ truncated filtration. -/
private theorem truncatedUC_assocGraded_one
    (cm : ConvergenceMorphism conv₁ conv₂) (s₀ : ℤ) (t : ω') (s : ℤ) :
    (truncatedUnderlyingComplex cm s₀ t).assocGraded s 1 =
      (F₁.truncatedFiltration s₀).associatedGraded s t := by
  simp only [truncatedUnderlyingComplex, underlyingComplex,
    FilteredComplex.assocGraded, Filtration.associatedGraded, twoTermFil]
  congr 1

/-- The assocGraded of the truncated underlying complex at k=0 equals
    the associatedGraded of the F₂ truncated filtration. -/
private theorem truncatedUC_assocGraded_zero
    (cm : ConvergenceMorphism conv₁ conv₂) (s₀ : ℤ) (t : ω') (s : ℤ) :
    (truncatedUnderlyingComplex cm s₀ t).assocGraded s 0 =
      (F₂.truncatedFiltration s₀).associatedGraded s t := by
  simp only [truncatedUnderlyingComplex, underlyingComplex,
    FilteredComplex.assocGraded, Filtration.associatedGraded, twoTermFil]
  congr 1

/-- 规范投影在复形次数 `1` 的关联分次映射就是第一个过滤的截断投影。 -/
private theorem unboundedUCProjection_assocGradedMap_one
    (cm : ConvergenceMorphism conv₁ conv₂) (s₀ : ℤ) (t : ω') (s : ℤ) :
    (unboundedUnderlyingComplexProjection cm s₀ t).assocGradedMap s 1 =
      eqToHom (unboundedUC_assocGraded_one cm t s) ≫
        F₁.toTruncatedAssociatedGraded s₀ s t ≫
        eqToHom (truncatedUC_assocGraded_one cm s₀ t s).symm := by
  let g := unboundedUnderlyingComplexProjection cm s₀ t
  let p : Subobject.underlying.obj ((unboundedUnderlyingComplex cm t).fil s 1) ⟶
      Subobject.underlying.obj ((truncatedUnderlyingComplex cm s₀ t).fil s 1) := by
    simpa [unboundedUnderlyingComplex, truncatedUnderlyingComplex,
      underlyingComplex, twoTermFil, twoTermObj] using
      F₁.toTruncatedFiltration s₀ s t
  have hp : p ≫ ((truncatedUnderlyingComplex cm s₀ t).fil s 1).arrow =
      ((unboundedUnderlyingComplex cm t).fil s 1).arrow ≫ g.f 1 := by
    simpa [p, g, unboundedUnderlyingComplexProjection,
      unboundedUnderlyingComplex, truncatedUnderlyingComplex,
      underlyingComplex, underlyingComplexMorphism, twoTermFil, twoTermObj] using
      F₁.toTruncatedFiltration_arrow s₀ s t
  have hlift : (g.filt_compat s 1).choose = p := by
    apply (cancel_mono ((truncatedUnderlyingComplex cm s₀ t).fil s 1).arrow).1
    rw [(g.filt_compat s 1).choose_spec, hp]
  change g.assocGradedMap s 1 = _
  apply (cancel_epi (cokernel.π _)).1
  simp only [FilteredComplexMorphism.assocGradedMap, cokernel.π_desc]
  rw [hlift]
  simp [p, g, unboundedUnderlyingComplexProjection,
    unboundedUnderlyingComplex, truncatedUnderlyingComplex,
    underlyingComplex, FilteredComplex.assocGraded,
    Filtration.associatedGraded, twoTermFil, twoTermObj,
    Filtration.toTruncatedAssociatedGraded]

/-- 规范投影在复形次数 `0` 的关联分次映射就是第二个过滤的截断投影。 -/
private theorem unboundedUCProjection_assocGradedMap_zero
    (cm : ConvergenceMorphism conv₁ conv₂) (s₀ : ℤ) (t : ω') (s : ℤ) :
    (unboundedUnderlyingComplexProjection cm s₀ t).assocGradedMap s 0 =
      eqToHom (unboundedUC_assocGraded_zero cm t s) ≫
        F₂.toTruncatedAssociatedGraded s₀ s t ≫
        eqToHom (truncatedUC_assocGraded_zero cm s₀ t s).symm := by
  let g := unboundedUnderlyingComplexProjection cm s₀ t
  let p : Subobject.underlying.obj ((unboundedUnderlyingComplex cm t).fil s 0) ⟶
      Subobject.underlying.obj ((truncatedUnderlyingComplex cm s₀ t).fil s 0) := by
    simpa [unboundedUnderlyingComplex, truncatedUnderlyingComplex,
      underlyingComplex, twoTermFil, twoTermObj] using
      F₂.toTruncatedFiltration s₀ s t
  have hp : p ≫ ((truncatedUnderlyingComplex cm s₀ t).fil s 0).arrow =
      ((unboundedUnderlyingComplex cm t).fil s 0).arrow ≫ g.f 0 := by
    simpa [p, g, unboundedUnderlyingComplexProjection,
      unboundedUnderlyingComplex, truncatedUnderlyingComplex,
      underlyingComplex, underlyingComplexMorphism, twoTermFil, twoTermObj] using
      F₂.toTruncatedFiltration_arrow s₀ s t
  have hlift : (g.filt_compat s 0).choose = p := by
    apply (cancel_mono ((truncatedUnderlyingComplex cm s₀ t).fil s 0).arrow).1
    rw [(g.filt_compat s 0).choose_spec, hp]
  change g.assocGradedMap s 0 = _
  apply (cancel_epi (cokernel.π _)).1
  simp only [FilteredComplexMorphism.assocGradedMap, cokernel.π_desc]
  rw [hlift]
  simp [p, g, unboundedUnderlyingComplexProjection,
    unboundedUnderlyingComplex, truncatedUnderlyingComplex,
    underlyingComplex, FilteredComplex.assocGraded,
    Filtration.associatedGraded, twoTermFil, twoTermObj,
    Filtration.toTruncatedAssociatedGraded]

/-- 两项复形次数之外，截断底层复形的对象为零。 -/
private theorem truncatedUC_obj_other
    (cm : ConvergenceMorphism conv₁ conv₂) (s₀ : ℤ) (t : ω') (k : ℤ)
    (h₁ : k ≠ 1) (h₀ : k ≠ 0) :
    (truncatedUnderlyingComplex cm s₀ t).A k = ⊥_ C := by
  simp [truncatedUnderlyingComplex, underlyingComplex, twoTermObj, h₁, h₀]

/-- 两项复形次数之外，截断复形的关联分次为零对象。 -/
private theorem truncatedUC_assocGraded_isZero_other
    (cm : ConvergenceMorphism conv₁ conv₂) (s₀ : ℤ) (t : ω') (s k : ℤ)
    (h₁ : k ≠ 1) (h₀ : k ≠ 0) :
    IsZero ((truncatedUnderlyingComplex cm s₀ t).assocGraded s k) := by
  have hA : IsZero ((truncatedUnderlyingComplex cm s₀ t).A k) := by
    rw [truncatedUC_obj_other cm s₀ t k h₁ h₀]
    exact IsInitial.isZero initialIsInitial
  have hFil : IsZero
      (Subobject.underlying.obj ((truncatedUnderlyingComplex cm s₀ t).fil s k)) :=
    hA.of_mono ((truncatedUnderlyingComplex cm s₀ t).fil s k).arrow
  exact hFil.of_epi (cokernel.π (Subobject.ofLE
    ((truncatedUnderlyingComplex cm s₀ t).fil (s + 1) k)
    ((truncatedUnderlyingComplex cm s₀ t).fil s k)
    ((truncatedUnderlyingComplex cm s₀ t).fil_anti s k)))

/-- 当当前过滤次数不超过截断层时，未截断与截断复形的零页规范同构。 -/
private noncomputable def unboundedUCAssocGradedProjectionIso
    (cm : ConvergenceMorphism conv₁ conv₂) (s₀ : ℤ) (t : ω')
    (s k : ℤ) (hs : s ≤ s₀) :
    (unboundedUnderlyingComplex cm t).assocGraded s k ≅
      (truncatedUnderlyingComplex cm s₀ t).assocGraded s k := by
  by_cases h₁ : k = 1
  · subst h₁
    exact eqToIso (unboundedUC_assocGraded_one cm t s) ≪≫
      F₁.truncatedAssociatedGradedIso s₀ s t hs ≪≫
      eqToIso (truncatedUC_assocGraded_one cm s₀ t s).symm
  by_cases h₀ : k = 0
  · subst h₀
    exact eqToIso (unboundedUC_assocGraded_zero cm t s) ≪≫
      F₂.truncatedAssociatedGradedIso s₀ s t hs ≪≫
      eqToIso (truncatedUC_assocGraded_zero cm s₀ t s).symm
  · exact IsZero.iso
      (unboundedUC_assocGraded_isZero_other cm t s k h₁ h₀)
      (truncatedUC_assocGraded_isZero_other cm s₀ t s k h₁ h₀)

/-- 未截断到截断复形的规范投影在有限窗口内恰为上述零页同构。 -/
private theorem unboundedUCProjection_assocGradedMap_eq_iso_hom
    (cm : ConvergenceMorphism conv₁ conv₂) (s₀ : ℤ) (t : ω')
    (s k : ℤ) (hs : s ≤ s₀) :
    (unboundedUnderlyingComplexProjection cm s₀ t).assocGradedMap s k =
      (unboundedUCAssocGradedProjectionIso cm s₀ t s k hs).hom := by
  by_cases h₁ : k = 1
  · subst h₁
    rw [unboundedUCProjection_assocGradedMap_one cm s₀ t s]
    change _ = eqToHom (unboundedUC_assocGraded_one cm t s) ≫
      (F₁.truncatedAssociatedGradedIso s₀ s t hs).hom ≫
      eqToHom (truncatedUC_assocGraded_one cm s₀ t s).symm
    congr 1
  by_cases h₀ : k = 0
  · subst h₀
    rw [unboundedUCProjection_assocGradedMap_zero cm s₀ t s]
    change _ = eqToHom (unboundedUC_assocGraded_zero cm t s) ≫
      (F₂.truncatedAssociatedGradedIso s₀ s t hs).hom ≫
      eqToHom (truncatedUC_assocGraded_zero cm s₀ t s).symm
    congr 1
  · exact (unboundedUC_assocGraded_isZero_other
      cm t s k h₁ h₀).eq_of_src _ _

/-- 若截断核已经包含在给定过滤层中，则先截断环境对象再除以该过滤层，
与直接除以原过滤层所得的余核规范同构。这个引理将有限循环条件中的
目标商对象与未截断商对象作比较。 -/
private noncomputable def filtrationCokernelTruncationIso
    {A : ω' → C} (fil : Filtration A) (s₀ q : ℤ) (k : ω')
    (hq : q ≤ s₀ + 1) :
    cokernel (fil.F q k).arrow ≅
      cokernel ((fil.truncatedFiltration s₀).F q k).arrow := by
  let Fq := fil.F q k
  let K := fil.F (s₀ + 1) k
  let Iq := (fil.truncatedFiltration s₀).F q k
  let p : A k ⟶ fil.truncatedObj s₀ k := fil.truncationProj s₀ k
  let pF : Subobject.underlying.obj Fq ⟶
      Subobject.underlying.obj Iq := fil.toTruncatedFiltration s₀ q k
  let πF : A k ⟶ cokernel Fq.arrow :=
    cokernel.π Fq.arrow
  let πI : fil.truncatedObj s₀ k ⟶ cokernel Iq.arrow :=
    cokernel.π Iq.arrow
  have hK : K ≤ Fq := fil.mono_of_le hq k
  have hKzero : K.arrow ≫ πF = 0 := by
    calc
      K.arrow ≫ πF = Subobject.ofLE K Fq hK ≫ (Fq.arrow ≫ πF) := by
        rw [← Category.assoc, Subobject.ofLE_arrow]
      _ = 0 := by rw [cokernel.condition, comp_zero]
  let backBase : fil.truncatedObj s₀ k ⟶ cokernel Fq.arrow :=
    cokernel.desc K.arrow πF hKzero
  have hp_back : p ≫ backBase = πF := by
    exact cokernel.π_desc _ _ _
  have hpF_arrow : pF ≫ Iq.arrow = Fq.arrow ≫ p := by
    exact fil.toTruncatedFiltration_arrow s₀ q k
  have hIzero : Iq.arrow ≫ backBase = 0 := by
    haveI : Epi pF := by
      dsimp only [pF, Filtration.toTruncatedFiltration]
      infer_instance
    apply (cancel_epi pF).1
    calc
      pF ≫ (Iq.arrow ≫ backBase) =
          (pF ≫ Iq.arrow) ≫ backBase := (Category.assoc _ _ _).symm
      _ = (Fq.arrow ≫ p) ≫ backBase := by rw [hpF_arrow]
      _ = Fq.arrow ≫ (p ≫ backBase) := Category.assoc _ _ _
      _ = Fq.arrow ≫ πF := by rw [hp_back]
      _ = 0 := cokernel.condition _
      _ = pF ≫ 0 := by simp
  let invMap : cokernel Iq.arrow ⟶ cokernel Fq.arrow :=
    cokernel.desc Iq.arrow backBase hIzero
  let homMap : cokernel Fq.arrow ⟶ cokernel Iq.arrow :=
    cokernel.map Fq.arrow Iq.arrow pF p hpF_arrow.symm
  have hπF_hom : πF ≫ homMap = p ≫ πI := by
    exact cokernel.π_desc _ _ _
  have hπI_inv : πI ≫ invMap = backBase := by
    exact cokernel.π_desc _ _ _
  haveI : Epi πF := by
    dsimp only [πF]
    infer_instance
  haveI : Epi πI := by
    dsimp only [πI]
    infer_instance
  haveI : Epi p := by
    dsimp only [p, Filtration.truncationProj]
    infer_instance
  refine
    { hom := homMap
      inv := invMap
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply (cancel_epi πF).1
    calc
      πF ≫ (homMap ≫ invMap) = (πF ≫ homMap) ≫ invMap :=
        (Category.assoc _ _ _).symm
      _ = (p ≫ πI) ≫ invMap := by rw [hπF_hom]
      _ = p ≫ (πI ≫ invMap) := Category.assoc _ _ _
      _ = p ≫ backBase := by rw [hπI_inv]
      _ = πF := hp_back
      _ = πF ≫ 𝟙 _ := (Category.comp_id _).symm
  · apply (cancel_epi πI).1
    calc
      πI ≫ (invMap ≫ homMap) = (πI ≫ invMap) ≫ homMap :=
        (Category.assoc _ _ _).symm
      _ = backBase ≫ homMap := by rw [hπI_inv]
      _ = πI := by
        apply (cancel_epi p).1
        calc
          p ≫ (backBase ≫ homMap) = (p ≫ backBase) ≫ homMap :=
            (Category.assoc _ _ _).symm
          _ = πF ≫ homMap := by rw [hp_back]
          _ = p ≫ πI := hπF_hom
      _ = πI ≫ 𝟙 _ := (Category.comp_id _).symm

/-- 截断投影的核包含在每个位于截断层以下的过滤层中。 -/
private theorem kernelSubobject_truncationProj_le
    {A : ω' → C} (fil : Filtration A) (s₀ s : ℤ) (k : ω')
    (hs : s ≤ s₀ + 1) :
    kernelSubobject (fil.truncationProj s₀ k) ≤ fil.F s k := by
  let K := fil.F (s₀ + 1) k
  let p := fil.truncationProj s₀ k
  have hK : K ≤ fil.F s k := fil.mono_of_le hs k
  let liftK : kernel p ⟶ (K : C) :=
    Abelian.monoLift K.arrow (kernel.ι p) (by
      dsimp only [p, Filtration.truncationProj]
      exact kernel.condition _)
  refine Subobject.le_of_comm
    ((kernelSubobjectIso p).hom ≫ liftK ≫
      Subobject.ofLE K (fil.F s k) hK) ?_
  simp only [Category.assoc, Subobject.ofLE_arrow]
  dsimp only [liftK]
  rw [Abelian.monoLift_comp]
  exact kernelSubobject_arrow p

/-- 在保留当前过滤次数时，截断转移在两项复形的零页上是同构。 -/
private noncomputable def truncatedUCAssocGradedTransitionIso
    (cm : ConvergenceMorphism conv₁ conv₂) {s₀ s₁ : ℤ} (h : s₀ ≤ s₁)
    (t : ω') (s k : ℤ) (hs : s ≤ s₀) :
    (truncatedUnderlyingComplex cm s₁ t).assocGraded s k ≅
      (truncatedUnderlyingComplex cm s₀ t).assocGraded s k := by
  by_cases h₁ : k = 1
  · subst h₁
    exact eqToIso (truncatedUC_assocGraded_one cm s₁ t s) ≪≫
      truncatedAssociatedGradedTransitionIso₁ (F₁ := F₁) h s t hs ≪≫
      eqToIso (truncatedUC_assocGraded_one cm s₀ t s).symm
  by_cases h₀ : k = 0
  · subst h₀
    exact eqToIso (truncatedUC_assocGraded_zero cm s₁ t s) ≪≫
      truncatedAssociatedGradedTransitionIso₂ (F₂ := F₂) h s t hs ≪≫
      eqToIso (truncatedUC_assocGraded_zero cm s₀ t s).symm
  · exact IsZero.iso
      (truncatedUC_assocGraded_isZero_other cm s₁ t s k h₁ h₀)
      (truncatedUC_assocGraded_isZero_other cm s₀ t s k h₁ h₀)

/-- 次数 `1` 的原始 `E₁∞` 环境对象与充分深截断复形的 `E₀` 项之间的同构。 -/
noncomputable def unboundedExtensionVOneTruncatedIso
    (cm : ConvergenceMorphism conv₁ conv₂) (s₀ : ℤ) (t : ω') (s : ℤ)
    (hs : s ≤ s₀) :
    unboundedExtensionV conv₁ conv₂ t (s, 1) ≅
      (truncatedUnderlyingComplex cm s₀ t).assocGraded s 1 :=
  unboundedExtensionVOneIso conv₁ conv₂ t s ≪≫
    F₁.truncatedAssociatedGradedIso s₀ s t hs ≪≫
    eqToIso (truncatedUC_assocGraded_one cm s₀ t s).symm

/-- 次数 `0` 的原始 `E₂∞` 环境对象与充分深截断复形的 `E₀` 项之间的同构。 -/
noncomputable def unboundedExtensionVZeroTruncatedIso
    (cm : ConvergenceMorphism conv₁ conv₂) (s₀ : ℤ) (t : ω') (s : ℤ)
    (hs : s ≤ s₀) :
    unboundedExtensionV conv₁ conv₂ t (s, 0) ≅
      (truncatedUnderlyingComplex cm s₀ t).assocGraded s 0 :=
  unboundedExtensionVZeroIso conv₁ conv₂ t s ≪≫
    F₂.truncatedAssociatedGradedIso s₀ s t hs ≪≫
    eqToIso (truncatedUC_assocGraded_zero cm s₀ t s).symm

private lemma imageSubobject_eq_top_of_zero_comp_epi {X Y Z : C}
    (g : X ⟶ Y) [Epi g] :
    imageSubobject ((kernelSubobject (0 : X ⟶ Z)).arrow ≫ g) = ⊤ := by
  haveI : IsIso (kernelSubobject (0 : X ⟶ Z)).arrow := isIso_kernelSubobject_zero_arrow
  have : Epi ((kernelSubobject (0 : X ⟶ Z)).arrow ≫ g) := epi_comp _ _
  have : Epi (imageSubobject ((kernelSubobject (0 : X ⟶ Z)).arrow ≫ g)).arrow :=
    epi_of_epi_fac (imageSubobject_arrow_comp _)
  haveI : IsIso (imageSubobject ((kernelSubobject (0 : X ⟶ Z)).arrow ≫ g)).arrow :=
    isIso_of_mono_of_epi _
  exact Subobject.eq_top_of_isIso_arrow _

private lemma imageSubobject_ofLE_bot_comp_eq_bot {X : C} (a : Subobject X)
    {Y : C} (g : Subobject.underlying.obj a ⟶ Y) :
    imageSubobject (Subobject.ofLE ⊥ a bot_le ≫ g) = ⊥ := by
  have h : Subobject.ofLE (⊥ : Subobject X) a bot_le = 0 := by
    have h1 := Subobject.ofLE_arrow (X := (⊥ : Subobject X)) (Y := a) bot_le
    rw [Subobject.bot_arrow] at h1
    exact (cancel_mono a.arrow).mp (by simp [h1])
  simp [h, zero_comp, imageSubobject_zero]

/-- 任意过滤复形的第零个有限边缘层为零。 -/
private theorem filteredComplex_boundarySubobject_zero_eq_bot
    (FC : FilteredComplex C) (s k : ℤ) :
    FC.boundarySubobject s k (0 : WithTop ℕ) = ⊥ := by
  let q : ℤ := s - (↑(0 : ℕ) : ℤ) + 1
  let eDeg : (k + 1) - 1 = k := by omega
  let eSub := congr_arg
    (fun j => Subobject.underlying.obj (FC.fil q j)) eDeg
  let eA := congr_arg FC.A eDeg
  let φ := FC.filDiff q (k + 1) ≫ eqToHom eSub
  have htransport : eqToHom eSub ≫ (FC.fil q k).arrow =
      (FC.fil q ((k + 1) - 1)).arrow ≫ eqToHom eA := by
    have hgeneral : ∀ (a b : ℤ) (h : a = b),
        eqToHom (congr_arg
            (fun j => Subobject.underlying.obj (FC.fil q j)) h) ≫
            (FC.fil q b).arrow =
          (FC.fil q a).arrow ≫ eqToHom (congr_arg FC.A h) := by
      intro a b h
      subst h
      simp
    exact hgeneral ((k + 1) - 1) k eDeg
  have hφ : φ ≫ (FC.fil q k).arrow =
      (FC.fil q (k + 1)).arrow ≫ FC.dToK k := by
    unfold φ FilteredComplex.dToK
    rw [Category.assoc, htransport, ← Category.assoc,
      FC.filDiff_comp_arrow]
    simp only [Category.assoc]
  let J := imageSubobject
    ((FC.fil q (k + 1)).arrow ≫ FC.dToK k)
  let I := J ⊓ FC.fil s k
  have hJ : J ≤ FC.fil q k :=
    imageSubobject_le _ φ hφ
  have hI : I ≤ FC.fil q k := le_trans inf_le_left hJ
  have hq : FC.fil q k ≤ FC.fil (s + 1) k := by
    apply le_of_eq
    congr 1
    dsimp only [q]
    omega
  have hI' : I ≤ FC.fil (s + 1) k := le_trans hI hq
  have hinc : Subobject.ofLE I (FC.fil s k) inf_le_right =
      Subobject.ofLE I (FC.fil (s + 1) k) hI' ≫
        Subobject.ofLE (FC.fil (s + 1) k) (FC.fil s k)
          (FC.fil_anti s k) := by
    apply (cancel_mono (FC.fil s k).arrow).1
    simp only [Category.assoc, Subobject.ofLE_arrow]
  have hzero : Subobject.ofLE I (FC.fil s k) inf_le_right ≫
      FC.filToAssocGraded s k = 0 := by
    rw [hinc, Category.assoc]
    change Subobject.ofLE I (FC.fil (s + 1) k) hI' ≫
      (Subobject.ofLE (FC.fil (s + 1) k) (FC.fil s k)
        (FC.fil_anti s k) ≫
        cokernel.π (Subobject.ofLE (FC.fil (s + 1) k) (FC.fil s k)
          (FC.fil_anti s k))) = 0
    rw [cokernel.condition, comp_zero]
  simp only [FilteredComplex.boundarySubobject]
  change imageSubobject
      (Subobject.ofLE I (FC.fil s k) inf_le_right ≫
        FC.filToAssocGraded s k) = ⊥
  apply le_antisymm
  · exact imageSubobject_le (X := ⊥)
      (Subobject.ofLE I (FC.fil s k) inf_le_right ≫
        FC.filToAssocGraded s k)
      (0 : Subobject.underlying.obj I ⟶
        Subobject.underlying.obj (⊥ : Subobject (FC.assocGraded s k)))
      (by simpa using hzero.symm)
  · exact bot_le

/-- 过滤复形的第零个有限页规范同构于它的关联分次。 -/
private noncomputable def filteredComplexFinitePageZeroIso
    (FC : FilteredComplex C) (s k : ℤ) :
    FC.finitePage s k 0 ≅ FC.assocGraded s k := by
  unfold FilteredComplex.finitePage
  let B := FC.boundarySubobject s k ((0 : ℕ) : WithTop ℕ)
  let Z := FC.cycleSubobject s k ((0 : ℕ) : WithTop ℕ)
  have hB : B = ⊥ := filteredComplex_boundarySubobject_zero_eq_bot FC s k
  have hZ : Z = ⊤ := FC.cycleSubobject_zero_eq_top s k
  have hBZ : B ≤ Z := by rw [hB, hZ]; exact bot_le
  change cokernel (Subobject.ofLE B Z hBZ) ≅ FC.assocGraded s k
  let p : Subobject.underlying.obj B ≅
      Subobject.underlying.obj (⊥ : Subobject (FC.assocGraded s k)) :=
    eqToIso (congr_arg Subobject.underlying.obj hB)
  let q : Subobject.underlying.obj Z ≅
      Subobject.underlying.obj (⊤ : Subobject (FC.assocGraded s k)) :=
    eqToIso (congr_arg Subobject.underlying.obj hZ)
  have hp : p.hom ≫ (⊥ : Subobject (FC.assocGraded s k)).arrow = B.arrow := by
    change eqToHom (congr_arg Subobject.underlying.obj hB) ≫
      (⊥ : Subobject (FC.assocGraded s k)).arrow = B.arrow
    exact Subobject.arrow_congr B ⊥ hB
  have hq : q.hom ≫ (⊤ : Subobject (FC.assocGraded s k)).arrow = Z.arrow := by
    change eqToHom (congr_arg Subobject.underlying.obj hZ) ≫
      (⊤ : Subobject (FC.assocGraded s k)).arrow = Z.arrow
    exact Subobject.arrow_congr Z ⊤ hZ
  have hsquare : Subobject.ofLE B Z hBZ ≫ q.hom =
      p.hom ≫ Subobject.ofLE
        (⊥ : Subobject (FC.assocGraded s k)) ⊤ bot_le := by
    apply (cancel_mono (⊤ : Subobject (FC.assocGraded s k)).arrow).1
    simp only [Category.assoc, hq, Subobject.ofLE_arrow, hp]
  have hzero : Subobject.ofLE (⊥ : Subobject (FC.assocGraded s k)) ⊤ bot_le = 0 := by
    apply (cancel_mono (⊤ : Subobject (FC.assocGraded s k)).arrow).1
    rw [Subobject.ofLE_arrow, Subobject.bot_arrow, zero_comp]
  exact cokernel.mapIso (Subobject.ofLE B Z hBZ)
      (Subobject.ofLE (⊥ : Subobject (FC.assocGraded s k)) ⊤ bot_le)
      p q hsquare ≪≫ cokernelIsoOfEq hzero ≪≫
    cokernelZeroIsoTarget ≪≫
    asIso (⊤ : Subobject (FC.assocGraded s k)).arrow

/-- 关联分次为零时，该双次数上的任意有限页也为零。 -/
private theorem filteredComplexFinitePageIsZero
    (FC : FilteredComplex C) (s k : ℤ) (n : ℕ)
    (h : IsZero (FC.assocGraded s k)) :
    IsZero (FC.finitePage s k n) := by
  have hZ : IsZero
      (Subobject.underlying.obj (FC.cycleSubobject s k (n : WithTop ℕ))) :=
    h.of_mono (FC.cycleSubobject s k (n : WithTop ℕ)).arrow
  haveI : Epi (FC.finitePageπ s k n) := by
    unfold FilteredComplex.finitePageπ
    infer_instance
  exact hZ.of_epi (FC.finitePageπ s k n)

/-- 截断层覆盖当前过滤次数时，未截断与截断两项复形的第零有限页同构。 -/
private noncomputable def unboundedFinitePageZeroTruncatedIso
    (cm : ConvergenceMorphism conv₁ conv₂) (s₀ : ℤ) (t : ω')
    (s k : ℤ) (hs : s ≤ s₀) :
    (unboundedUnderlyingComplex cm t).finitePage s k 0 ≅
      (truncatedUnderlyingComplex cm s₀ t).finitePage s k 0 :=
  filteredComplexFinitePageZeroIso (unboundedUnderlyingComplex cm t) s k ≪≫
    unboundedUCAssocGradedProjectionIso cm s₀ t s k hs ≪≫
    (filteredComplexFinitePageZeroIso
      (truncatedUnderlyingComplex cm s₀ t) s k).symm

private theorem truncatedUC_cycleSubobject_zero_eq_top
    (cm : ConvergenceMorphism conv₁ conv₂) (s₀ : ℤ) (t : ω') (s : ℤ)
    (r : WithTop ℕ) :
    (truncatedUnderlyingComplex cm s₀ t).cycleSubobject s 0 r = ⊤ := by
  have h_d_zero : (truncatedUnderlyingComplex cm s₀ t).d 0 = 0 := by
    simp [truncatedUnderlyingComplex, underlyingComplex, twoTermDiff]
  delta FilteredComplex.cycleSubobject
  cases r with
  | top =>
    dsimp only []
    convert imageSubobject_eq_top_of_zero_comp_epi
      (Z := (truncatedUnderlyingComplex cm s₀ t).A (0 - 1))
      (cokernel.π (((truncatedUnderlyingComplex cm s₀ t).fil (s + 1) 0).ofLE
        ((truncatedUnderlyingComplex cm s₀ t).fil s 0) (FilteredComplex.fil_anti _ s 0)))
      <;> first | rfl | rw [h_d_zero, comp_zero]
  | coe n =>
    dsimp only []
    convert imageSubobject_eq_top_of_zero_comp_epi
      (Z := cokernel ((truncatedUnderlyingComplex cm s₀ t).fil (s + ↑n) (0 - 1)).arrow)
      (cokernel.π (((truncatedUnderlyingComplex cm s₀ t).fil (s + 1) 0).ofLE
        ((truncatedUnderlyingComplex cm s₀ t).fil s 0) (FilteredComplex.fil_anti _ s 0)))
      <;> first | rfl | simp [h_d_zero, comp_zero, zero_comp]

private theorem truncatedUC_boundarySubobject_one_eq_bot
    (cm : ConvergenceMorphism conv₁ conv₂) (s₀ : ℤ) (t : ω') (s : ℤ)
    (r : WithTop ℕ) :
    (truncatedUnderlyingComplex cm s₀ t).boundarySubobject s 1 r = ⊥ := by
  have h_dToK_zero : (truncatedUnderlyingComplex cm s₀ t).dToK 1 = 0 := by
    simp [FilteredComplex.dToK, truncatedUnderlyingComplex, underlyingComplex, twoTermDiff]
  delta FilteredComplex.boundarySubobject
  cases r with
  | top =>
    dsimp only []
    have h_I : imageSubobject ((truncatedUnderlyingComplex cm s₀ t).dToK 1) ⊓
        (truncatedUnderlyingComplex cm s₀ t).fil s 1 = ⊥ := by
      rw [h_dToK_zero, imageSubobject_zero, bot_inf_eq]
    convert imageSubobject_ofLE_bot_comp_eq_bot
      ((truncatedUnderlyingComplex cm s₀ t).fil s 1)
      (cokernel.π (((truncatedUnderlyingComplex cm s₀ t).fil (s + 1) 1).ofLE
        ((truncatedUnderlyingComplex cm s₀ t).fil s 1) (FilteredComplex.fil_anti _ s 1)))
      <;> first | rfl | simpa using h_I
  | coe n =>
    dsimp only []
    have h_I : imageSubobject
        (((truncatedUnderlyingComplex cm s₀ t).fil (s - ↑n + 1) 2).arrow ≫
          (truncatedUnderlyingComplex cm s₀ t).dToK 1) ⊓
        (truncatedUnderlyingComplex cm s₀ t).fil s 1 = ⊥ := by
      rw [h_dToK_zero, comp_zero, imageSubobject_zero, bot_inf_eq]
    convert imageSubobject_ofLE_bot_comp_eq_bot
      ((truncatedUnderlyingComplex cm s₀ t).fil s 1)
      (cokernel.π (((truncatedUnderlyingComplex cm s₀ t).fil (s + 1) 1).ofLE
        ((truncatedUnderlyingComplex cm s₀ t).fil s 1)
        (FilteredComplex.fil_anti _ s 1)))
      <;> first | rfl | simpa using h_I

/-- 未截断二项复形在次数 `0` 的循环层恒为顶子对象。 -/
private theorem unboundedUC_cycleSubobject_zero_eq_top
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω') (s : ℤ)
    (r : WithTop ℕ) :
    (unboundedUnderlyingComplex cm t).cycleSubobject s 0 r = ⊤ := by
  have h_d_zero : (unboundedUnderlyingComplex cm t).d 0 = 0 := by
    simp [unboundedUnderlyingComplex, underlyingComplex, twoTermDiff]
  delta FilteredComplex.cycleSubobject
  cases r with
  | top =>
    dsimp only []
    convert imageSubobject_eq_top_of_zero_comp_epi
      (Z := (unboundedUnderlyingComplex cm t).A (0 - 1))
      (cokernel.π (((unboundedUnderlyingComplex cm t).fil (s + 1) 0).ofLE
        ((unboundedUnderlyingComplex cm t).fil s 0)
        (FilteredComplex.fil_anti _ s 0)))
      <;> first | rfl | rw [h_d_zero, comp_zero]
  | coe n =>
    dsimp only []
    convert imageSubobject_eq_top_of_zero_comp_epi
      (Z := cokernel ((unboundedUnderlyingComplex cm t).fil
        (s + ↑n) (0 - 1)).arrow)
      (cokernel.π (((unboundedUnderlyingComplex cm t).fil (s + 1) 0).ofLE
        ((unboundedUnderlyingComplex cm t).fil s 0)
        (FilteredComplex.fil_anti _ s 0)))
      <;> first | rfl | simp [h_d_zero, comp_zero, zero_comp]

/-- 未截断二项复形在次数 `1` 的边缘层恒为底子对象。 -/
private theorem unboundedUC_boundarySubobject_one_eq_bot
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω') (s : ℤ)
    (r : WithTop ℕ) :
    (unboundedUnderlyingComplex cm t).boundarySubobject s 1 r = ⊥ := by
  have h_dToK_zero : (unboundedUnderlyingComplex cm t).dToK 1 = 0 := by
    simp [FilteredComplex.dToK, unboundedUnderlyingComplex,
      underlyingComplex, twoTermDiff]
  delta FilteredComplex.boundarySubobject
  cases r with
  | top =>
    dsimp only []
    have h_I : imageSubobject ((unboundedUnderlyingComplex cm t).dToK 1) ⊓
        (unboundedUnderlyingComplex cm t).fil s 1 = ⊥ := by
      rw [h_dToK_zero, imageSubobject_zero, bot_inf_eq]
    convert imageSubobject_ofLE_bot_comp_eq_bot
      ((unboundedUnderlyingComplex cm t).fil s 1)
      (cokernel.π (((unboundedUnderlyingComplex cm t).fil (s + 1) 1).ofLE
        ((unboundedUnderlyingComplex cm t).fil s 1)
        (FilteredComplex.fil_anti _ s 1)))
      <;> first | rfl | simpa using h_I
  | coe n =>
    dsimp only []
    have h_I : imageSubobject
        (((unboundedUnderlyingComplex cm t).fil (s - ↑n + 1) 2).arrow ≫
          (unboundedUnderlyingComplex cm t).dToK 1) ⊓
        (unboundedUnderlyingComplex cm t).fil s 1 = ⊥ := by
      rw [h_dToK_zero, comp_zero, imageSubobject_zero, bot_inf_eq]
    convert imageSubobject_ofLE_bot_comp_eq_bot
      ((unboundedUnderlyingComplex cm t).fil s 1)
      (cokernel.π (((unboundedUnderlyingComplex cm t).fil (s + 1) 1).ofLE
        ((unboundedUnderlyingComplex cm t).fil s 1)
        (FilteredComplex.fil_anti _ s 1)))
      <;> first | rfl | simpa using h_I

/-- 核交换方块的左边为满射、右边为单射时，诱导的核子对象映射为满射。 -/
private theorem kernelSubobjectMap_epi_of_epi_of_mono
    {X Y X' Y' : C} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (left : X ⟶ X') (right : Y ⟶ Y')
    (w : left ≫ f' = f ≫ right) [Epi left] [Mono right] :
    Epi (kernelSubobjectMap (Arrow.homMk' left right w)) := by
  let sq := Arrow.homMk' left right w
  apply CategoryTheory.Abelian.Pseudoelement.epi_of_pseudo_surjective
  intro y
  obtain ⟨x, hx⟩ :=
    CategoryTheory.Abelian.Pseudoelement.pseudo_surjective_of_epi left
      ((kernelSubobject f').arrow y)
  have hfx : f x = 0 := by
    apply CategoryTheory.Abelian.Pseudoelement.pseudo_injective_of_mono right
    calc
      right (f x) = (f ≫ right) x :=
        (CategoryTheory.Abelian.Pseudoelement.comp_apply f right x).symm
      _ = (left ≫ f') x := by rw [w]
      _ = f' (left x) :=
        CategoryTheory.Abelian.Pseudoelement.comp_apply left f' x
      _ = f' ((kernelSubobject f').arrow y) := by rw [hx]
      _ = ((kernelSubobject f').arrow ≫ f') y :=
        (CategoryTheory.Abelian.Pseudoelement.comp_apply _ _ y).symm
      _ = 0 := by rw [kernelSubobject_arrow_comp,
        CategoryTheory.Abelian.Pseudoelement.zero_apply]
      _ = right 0 :=
        (CategoryTheory.Abelian.Pseudoelement.apply_zero right).symm
  obtain ⟨z, hz⟩ :=
    CategoryTheory.Abelian.Pseudoelement.pseudo_exact_of_exact
      (ShortComplex.kernelSequence_exact f) x hfx
  let z' := (kernelSubobjectIso f).inv z
  refine ⟨z', ?_⟩
  apply CategoryTheory.Abelian.Pseudoelement.pseudo_injective_of_mono
    (kernelSubobject f').arrow
  calc
    (kernelSubobject f').arrow
        (kernelSubobjectMap (Arrow.homMk' left right w) z') =
        (kernelSubobjectMap (Arrow.homMk' left right w) ≫
          (kernelSubobject f').arrow) z' :=
      (CategoryTheory.Abelian.Pseudoelement.comp_apply _ _ z').symm
    _ = ((kernelSubobject f).arrow ≫ left) z' := by
      rw [kernelSubobjectMap_arrow]
      change ((kernelSubobject f).arrow ≫ left) z' = _
      rfl
    _ = left ((kernelSubobject f).arrow z') :=
      CategoryTheory.Abelian.Pseudoelement.comp_apply _ _ z'
    _ = left x := by
      rw [show (kernelSubobject f).arrow z' = x by
        calc
          (kernelSubobject f).arrow z' = (kernel.ι f) z := by
            simp [z', ← CategoryTheory.Abelian.Pseudoelement.comp_apply]
          _ = x := by
            simpa [ShortComplex.kernelSequence] using hz]
    _ = (kernelSubobject f').arrow y := hx

/-- 像交换方块的左边为满射时，诱导的像子对象映射仍为满射。 -/
private theorem imageSubobjectMap_epi_of_epi_left
    {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z}
    (left : W ⟶ Y) (right : X ⟶ Z)
    (w : left ≫ g = f ≫ right) [Epi left] :
    Epi (imageSubobjectMap (Arrow.homMk' left right w)) := by
  apply CategoryTheory.Abelian.Pseudoelement.epi_of_pseudo_surjective
  intro z
  obtain ⟨y, hy⟩ :=
    CategoryTheory.Abelian.Pseudoelement.pseudo_surjective_of_epi
      (factorThruImageSubobject g) z
  obtain ⟨x, hx⟩ :=
    CategoryTheory.Abelian.Pseudoelement.pseudo_surjective_of_epi left y
  let x' := factorThruImageSubobject f x
  refine ⟨x', ?_⟩
  apply CategoryTheory.Abelian.Pseudoelement.pseudo_injective_of_mono
    (imageSubobject g).arrow
  calc
    (imageSubobject g).arrow
        (imageSubobjectMap (Arrow.homMk' left right w) x') =
        (imageSubobjectMap (Arrow.homMk' left right w) ≫
          (imageSubobject g).arrow) x' :=
      (CategoryTheory.Abelian.Pseudoelement.comp_apply _ _ x').symm
    _ = ((imageSubobject f).arrow ≫ right) x' := by
      rw [imageSubobjectMap_arrow]
      change ((imageSubobject f).arrow ≫ right) x' = _
      rfl
    _ = right ((imageSubobject f).arrow x') :=
      CategoryTheory.Abelian.Pseudoelement.comp_apply _ _ x'
    _ = right (f x) := by
      rw [show (imageSubobject f).arrow x' = f x by
        simp [x', ← CategoryTheory.Abelian.Pseudoelement.comp_apply]]
    _ = (f ≫ right) x :=
      (CategoryTheory.Abelian.Pseudoelement.comp_apply _ _ x).symm
    _ = (left ≫ g) x := by rw [w]
    _ = g (left x) :=
      CategoryTheory.Abelian.Pseudoelement.comp_apply _ _ x
    _ = g y := by rw [hx]
    _ = (factorThruImageSubobject g ≫ (imageSubobject g).arrow) y := by
      rw [imageSubobject_arrow_comp]
    _ = (imageSubobject g).arrow z := by
      rw [CategoryTheory.Abelian.Pseudoelement.comp_apply, hy]

/-- 在商投影下，若投影核已包含在交中的第二个子对象内，
则两个子对象的满射所诱导的交上映射仍为满射。 -/
private theorem infLift_epi_of_epi_of_kernel_le
    {X Y : C} (p : X ⟶ Y)
    (J Q : Subobject X) (J' Q' : Subobject Y)
    (jMap : (J : C) ⟶ (J' : C)) (qMap : (Q : C) ⟶ (Q' : C))
    (hj : jMap ≫ J'.arrow = J.arrow ≫ p)
    (hq : qMap ≫ Q'.arrow = Q.arrow ≫ p)
    (hker : kernelSubobject p ≤ Q)
    (α : Subobject.underlying.obj (J ⊓ Q : Subobject X) ⟶
      Subobject.underlying.obj (J' ⊓ Q' : Subobject Y))
    (hα : α ≫ (J' ⊓ Q').arrow = (J ⊓ Q).arrow ≫ p)
    [Epi jMap] [Epi qMap] : Epi α := by
  apply CategoryTheory.Abelian.Pseudoelement.epi_of_pseudo_surjective
  intro y
  let yJ := Subobject.ofLE (J' ⊓ Q') J' inf_le_left y
  let yQ := Subobject.ofLE (J' ⊓ Q') Q' inf_le_right y
  obtain ⟨xJ, hxJ⟩ :=
    CategoryTheory.Abelian.Pseudoelement.pseudo_surjective_of_epi jMap yJ
  obtain ⟨xQ, hxQ⟩ :=
    CategoryTheory.Abelian.Pseudoelement.pseudo_surjective_of_epi qMap yQ
  have himage : p (J.arrow xJ) = p (Q.arrow xQ) := by
    calc
      p (J.arrow xJ) = (J.arrow ≫ p) xJ :=
        (CategoryTheory.Abelian.Pseudoelement.comp_apply _ _ _).symm
      _ = (jMap ≫ J'.arrow) xJ := by rw [hj]
      _ = J'.arrow (jMap xJ) :=
        CategoryTheory.Abelian.Pseudoelement.comp_apply _ _ _
      _ = J'.arrow yJ := by rw [hxJ]
      _ = (J' ⊓ Q').arrow y := by
        simp [yJ, ← CategoryTheory.Abelian.Pseudoelement.comp_apply]
      _ = Q'.arrow yQ := by
        simp [yQ, ← CategoryTheory.Abelian.Pseudoelement.comp_apply]
      _ = Q'.arrow (qMap xQ) := by rw [hxQ]
      _ = (qMap ≫ Q'.arrow) xQ :=
        (CategoryTheory.Abelian.Pseudoelement.comp_apply _ _ _).symm
      _ = (Q.arrow ≫ p) xQ := by rw [hq]
      _ = p (Q.arrow xQ) :=
        CategoryTheory.Abelian.Pseudoelement.comp_apply _ _ _
  obtain ⟨z, hpz, hz⟩ :=
    CategoryTheory.Abelian.Pseudoelement.sub_of_eq_image p
      (J.arrow xJ) (Q.arrow xQ) himage
  obtain ⟨kz, hkz⟩ :=
    CategoryTheory.Abelian.Pseudoelement.pseudo_exact_of_exact
      (ShortComplex.kernelSequence_exact p) z hpz
  let kz' := (kernelSubobjectIso p).inv kz
  have hQz : cokernel.π Q.arrow z = 0 := by
    calc
      cokernel.π Q.arrow z =
          cokernel.π Q.arrow ((kernelSubobject p).arrow kz') := by
        rw [show (kernelSubobject p).arrow kz' = z by
          calc
            (kernelSubobject p).arrow kz' = kernel.ι p kz := by
              simp [kz', ← CategoryTheory.Abelian.Pseudoelement.comp_apply]
            _ = z := by
              simpa [ShortComplex.kernelSequence] using hkz]
      _ = ((kernelSubobject p).arrow ≫ cokernel.π Q.arrow) kz' :=
        (CategoryTheory.Abelian.Pseudoelement.comp_apply _ _ _).symm
      _ = (Subobject.ofLE (kernelSubobject p) Q hker ≫
          Q.arrow ≫ cokernel.π Q.arrow) kz' := by
        rw [← Category.assoc, Subobject.ofLE_arrow]
      _ = 0 := by simp
  have hQx : cokernel.π Q.arrow (J.arrow xJ) = 0 := by
    rw [← hz (cokernel Q.arrow) (cokernel.π Q.arrow)]
    · exact hQz
    · rw [← CategoryTheory.Abelian.Pseudoelement.comp_apply,
        cokernel.condition, CategoryTheory.Abelian.Pseudoelement.zero_apply]
  obtain ⟨qx, hqx⟩ :=
    CategoryTheory.Abelian.Pseudoelement.pseudo_exact_of_exact
      (ShortComplex.cokernelSequence_exact Q.arrow) (J.arrow xJ) hQx
  obtain ⟨w, hw⟩ := CategoryTheory.Abelian.Pseudoelement.pseudo_pullback
    (f := J.arrow) (g := Q.arrow) (p := xJ) (q := qx) hqx.symm
  let hP := IsPullback.of_hasPullback J.arrow Q.arrow
  let hI := Subobject.inf_isPullback J Q
  let eI : pullback J.arrow Q.arrow ≅ (J ⊓ Q : Subobject X) :=
    hP.isoIsPullback _ _ hI
  let i := eI.hom w
  have heI_fst : eI.hom ≫ Subobject.ofLE (J ⊓ Q) J inf_le_left =
      pullback.fst J.arrow Q.arrow :=
    hP.isoIsPullback_hom_fst _ _ hI
  refine ⟨i, ?_⟩
  apply CategoryTheory.Abelian.Pseudoelement.pseudo_injective_of_mono
    (J' ⊓ Q').arrow
  calc
    (J' ⊓ Q').arrow (α i) = (α ≫ (J' ⊓ Q').arrow) i :=
      (CategoryTheory.Abelian.Pseudoelement.comp_apply _ _ _).symm
    _ = ((J ⊓ Q).arrow ≫ p) i := by rw [hα]
    _ = p ((J ⊓ Q).arrow i) :=
      CategoryTheory.Abelian.Pseudoelement.comp_apply _ _ _
    _ = p (J.arrow xJ) := by
      congr 1
      calc
        (J ⊓ Q).arrow i =
            (Subobject.ofLE (J ⊓ Q) J inf_le_left ≫ J.arrow) i := by
          rw [Subobject.inf_comp_left]
        _ = J.arrow
            (Subobject.ofLE (J ⊓ Q) J inf_le_left (eI.hom w)) := by
          rw [CategoryTheory.Abelian.Pseudoelement.comp_apply]
        _ = J.arrow (pullback.fst J.arrow Q.arrow w) := by
          rw [← CategoryTheory.Abelian.Pseudoelement.comp_apply eI.hom _ w,
            heI_fst]
        _ = J.arrow xJ := by rw [hw.1]
    _ = J'.arrow yJ := by
      calc
        p (J.arrow xJ) = (J.arrow ≫ p) xJ :=
          (CategoryTheory.Abelian.Pseudoelement.comp_apply _ _ _).symm
        _ = (jMap ≫ J'.arrow) xJ := by rw [hj]
        _ = J'.arrow (jMap xJ) :=
          CategoryTheory.Abelian.Pseudoelement.comp_apply _ _ _
        _ = J'.arrow yJ := by rw [hxJ]
    _ = (J' ⊓ Q').arrow y := by
      simp [yJ, ← CategoryTheory.Abelian.Pseudoelement.comp_apply]

/-- 满射前合成不改变像子对象。 -/
private theorem imageSubobject_epi_comp_eq
    {X Y Z : C} (e : X ⟶ Y) [Epi e] (f : Y ⟶ Z) :
    imageSubobject (e ≫ f) = imageSubobject f := by
  apply le_antisymm (imageSubobject_comp_le e f)
  have hle := imageSubobject_comp_le e f
  haveI : Epi (Subobject.ofLE _ _ hle) :=
    imageSubobject_comp_le_epi_of_epi e f
  haveI : IsIso (Subobject.ofLE _ _ hle) := isIso_of_mono_of_epi _
  exact Subobject.le_of_comm (inv (Subobject.ofLE _ _ hle))
    (by rw [IsIso.inv_comp_eq]; exact (Subobject.ofLE_arrow hle).symm)

/-- Given a commutative square on kernels and a compatible cokernel-projection square,
    imageSubobjectMap provides a lift for the composition `kernelSubobject.arrow ≫ πV`. -/
private lemma imageSubobjectMap_of_kernel_cokernel_square
    {X₁ Y₁ X₂ Y₂ V₁ V₂ : C}
    {f₁ : X₁ ⟶ Y₁} {f₂ : X₂ ⟶ Y₂}
    {left : X₁ ⟶ X₂} {right : Y₁ ⟶ Y₂}
    (sq_ker : left ≫ f₂ = f₁ ≫ right)
    {πV₁ : X₁ ⟶ V₁} {πV₂ : X₂ ⟶ V₂}
    {φ : V₁ ⟶ V₂}
    (h_πV : left ≫ πV₂ = πV₁ ≫ φ) :
    ∃ (lift : Subobject.underlying.obj (imageSubobject ((kernelSubobject f₁).arrow ≫ πV₁)) ⟶
              Subobject.underlying.obj (imageSubobject ((kernelSubobject f₂).arrow ≫ πV₂))),
      lift ≫ (imageSubobject ((kernelSubobject f₂).arrow ≫ πV₂)).arrow =
        (imageSubobject ((kernelSubobject f₁).arrow ≫ πV₁)).arrow ≫ φ := by
  let sq := Arrow.homMk (f := Arrow.mk f₁) (g := Arrow.mk f₂) left right sq_ker
  let ker_lift := kernelSubobjectMap sq
  have hker := kernelSubobjectMap_arrow sq
  have h_sq_left : sq.left = left := rfl
  have img_sq_comm : ker_lift ≫ ((kernelSubobject f₂).arrow ≫ πV₂) =
      ((kernelSubobject f₁).arrow ≫ πV₁) ≫ φ := by
    rw [Category.assoc, ← h_πV, ← Category.assoc, hker, h_sq_left, Category.assoc]
  let sq_img := Arrow.homMk
    (f := Arrow.mk ((kernelSubobject f₁).arrow ≫ πV₁))
    (g := Arrow.mk ((kernelSubobject f₂).arrow ≫ πV₂))
    ker_lift φ img_sq_comm
  exact ⟨imageSubobjectMap sq_img, imageSubobjectMap_arrow sq_img⟩

/-- 过滤复形态射在有限循环条件的目标商对象上诱导的映射。 -/
private noncomputable def filteredComplexMorphismCycleCokernelMap
    {X Y : FilteredComplex C} (g : FilteredComplexMorphism X Y)
    (s k : ℤ) (n : ℕ) :
    cokernel ((X.fil (s + ↑n) (k - 1)).arrow) ⟶
      cokernel ((Y.fil (s + ↑n) (k - 1)).arrow) :=
  cokernel.map
    ((X.fil (s + ↑n) (k - 1)).arrow)
    ((Y.fil (s + ↑n) (k - 1)).arrow)
    (g.filt_compat (s + ↑n) (k - 1)).choose
    (g.f (k - 1))
    (g.filt_compat (s + ↑n) (k - 1)).choose_spec.symm

/-- 有限循环条件的目标商映射与两个余核投影交换。 -/
private theorem filteredComplexMorphismCycleCokernelMap_π
    {X Y : FilteredComplex C} (g : FilteredComplexMorphism X Y)
    (s k : ℤ) (n : ℕ) :
    cokernel.π ((X.fil (s + ↑n) (k - 1)).arrow) ≫
        filteredComplexMorphismCycleCokernelMap g s k n =
      g.f (k - 1) ≫
        cokernel.π ((Y.fil (s + ↑n) (k - 1)).arrow) := by
  exact cokernel.π_desc _ _ _

/-- 若当前过滤层的提升为满射、循环条件的目标商映射为单射，且关联
分次映射是给定同构，则该同构精确地把源有限循环层送到目标循环层。 -/
private theorem filteredComplexMorphism_map_cycleSubobject_eq
    {X Y : FilteredComplex C} (g : FilteredComplexMorphism X Y)
    (s k : ℤ) (n : ℕ)
    (e : X.assocGraded s k ≅ Y.assocGraded s k)
    (he : g.assocGradedMap s k = e.hom)
    (hu : Epi (g.filt_compat s k).choose)
    (hq : Mono (filteredComplexMorphismCycleCokernelMap g s k n)) :
    (Subobject.mapIsoToOrderIso e) (X.cycleSubobject s k (n : WithTop ℕ)) =
      Y.cycleSubobject s k (n : WithTop ℕ) := by
  let u := (g.filt_compat s k).choose
  let q := filteredComplexMorphismCycleCokernelMap g s k n
  let πX := X.filToAssocGraded s k
  let πY := Y.filToAssocGraded s k
  let fX := (X.fil s k).arrow ≫ X.d k ≫
    cokernel.π ((X.fil (s + ↑n) (k - 1)).arrow)
  let fY := (Y.fil s k).arrow ≫ Y.d k ≫
    cokernel.π ((Y.fil (s + ↑n) (k - 1)).arrow)
  have hπ : u ≫ πY = πX ≫ e.hom := by
    rw [← he]
    unfold FilteredComplexMorphism.assocGradedMap πX πY
      FilteredComplex.filToAssocGraded
    exact (cokernel.π_desc _ _ _).symm
  have hsq : u ≫ fY = fX ≫ q := by
    calc
      u ≫ fY = (X.fil s k).arrow ≫ g.f k ≫ Y.d k ≫
          cokernel.π ((Y.fil (s + ↑n) (k - 1)).arrow) := by
        simp only [fY, ← Category.assoc]
        rw [(g.filt_compat s k).choose_spec]
      _ = (X.fil s k).arrow ≫ X.d k ≫ g.f (k - 1) ≫
          cokernel.π ((Y.fil (s + ↑n) (k - 1)).arrow) := by
        simpa only [Category.assoc] using congrArg
          (fun z => (X.fil s k).arrow ≫ z ≫
            cokernel.π ((Y.fil (s + ↑n) (k - 1)).arrow))
          (g.comm_d k)
      _ = (X.fil s k).arrow ≫ X.d k ≫
          cokernel.π ((X.fil (s + ↑n) (k - 1)).arrow) ≫ q := by
        rw [filteredComplexMorphismCycleCokernelMap_π]
      _ = fX ≫ q := by simp only [fX, Category.assoc]
  let kerMap := kernelSubobjectMap (Arrow.homMk' u q hsq)
  haveI : Epi u := hu
  haveI : Mono q := hq
  haveI : Epi kerMap := by
    dsimp only [kerMap]
    exact kernelSubobjectMap_epi_of_epi_of_mono u q hsq
  have hker : kerMap ≫ (kernelSubobject fY).arrow =
      (kernelSubobject fX).arrow ≫ u := by
    exact kernelSubobjectMap_arrow _
  have himage : imageSubobject
      (((kernelSubobject fX).arrow ≫ πX) ≫ e.hom) =
      imageSubobject ((kernelSubobject fY).arrow ≫ πY) := by
    calc
      imageSubobject (((kernelSubobject fX).arrow ≫ πX) ≫ e.hom) =
          imageSubobject ((kernelSubobject fX).arrow ≫ (πX ≫ e.hom)) := by
        simp only [Category.assoc]
      _ = imageSubobject ((kernelSubobject fX).arrow ≫ (u ≫ πY)) := by
        rw [hπ]
      _ = imageSubobject (((kernelSubobject fX).arrow ≫ u) ≫ πY) := by
        simp only [Category.assoc]
      _ = imageSubobject ((kerMap ≫ (kernelSubobject fY).arrow) ≫ πY) := by
        rw [hker]
      _ = imageSubobject
          (kerMap ≫ ((kernelSubobject fY).arrow ≫ πY)) := by
        simp only [Category.assoc]
      _ = imageSubobject ((kernelSubobject fY).arrow ≫ πY) :=
        imageSubobject_epi_comp_eq kerMap
          ((kernelSubobject fY).arrow ≫ πY)
  change (Subobject.map e.hom).obj
      (imageSubobject ((kernelSubobject fX).arrow ≫ πX)) =
    imageSubobject ((kernelSubobject fY).arrow ≫ πY)
  calc
    (Subobject.map e.hom).obj
        (imageSubobject ((kernelSubobject fX).arrow ≫ πX)) =
        imageSubobject
          (((kernelSubobject fX).arrow ≫ πX) ≫ e.hom) := by
      rw [← Subobject.mk_arrow
          (imageSubobject ((kernelSubobject fX).arrow ≫ πX)),
        Subobject.map_mk,
        ← Subobject.mk_arrow
          (imageSubobject
            (((kernelSubobject fX).arrow ≫ πX) ≫ e.hom))]
      exact Subobject.mk_eq_mk_of_comm _ _
        (imageSubobjectCompIso
          ((kernelSubobject fX).arrow ≫ πX) e.hom).symm
        (imageSubobjectCompIso_inv_arrow
          ((kernelSubobject fX).arrow ≫ πX) e.hom)
    _ = imageSubobject ((kernelSubobject fY).arrow ≫ πY) := himage

/-- 未截断投影在次数 `1` 的有限循环条件商上诱导的映射，
就是过滤层商的规范同构的正向映射。 -/
private theorem unboundedUCProjection_cycleCokernelMap_one_eq
    (cm : ConvergenceMorphism conv₁ conv₂) (s₀ : ℤ) (t : ω')
    (s : ℤ) (n : ℕ) (h : s + ↑n ≤ s₀ + 1) :
    filteredComplexMorphismCycleCokernelMap
        (unboundedUnderlyingComplexProjection cm s₀ t) s 1 n =
      (filtrationCokernelTruncationIso F₂ s₀ (s + ↑n) t h).hom := by
  apply (cancel_epi
    (cokernel.π ((unboundedUnderlyingComplex cm t).fil
      (s + ↑n) (1 - 1)).arrow)).1
  rw [filteredComplexMorphismCycleCokernelMap_π]
  change (unboundedUnderlyingComplexProjection cm s₀ t).f 0 ≫
      cokernel.π ((truncatedUnderlyingComplex cm s₀ t).fil
        (s + ↑n) 0).arrow = _
  rw [unboundedUCProjection_f_zero]
  change F₂.truncationProj s₀ t ≫
      cokernel.π ((F₂.truncatedFiltration s₀).F (s + ↑n) t).arrow = _
  unfold filtrationCokernelTruncationIso
  dsimp only
  exact (cokernel.π_desc _ _ _).symm

/-- 当截断层同时覆盖当前关联分次和有限循环的目标过滤层时，
规范投影精确地把次数 `1` 的未截断循环层送到截断循环层。 -/
private theorem unboundedUCProjection_map_cycleSubobject_one_eq
    (cm : ConvergenceMorphism conv₁ conv₂) (s₀ : ℤ) (t : ω')
    (s : ℤ) (n : ℕ) (hs : s ≤ s₀) (hcycle : s + ↑n ≤ s₀ + 1) :
    (Subobject.mapIsoToOrderIso
      (unboundedUCAssocGradedProjectionIso cm s₀ t s 1 hs))
        ((unboundedUnderlyingComplex cm t).cycleSubobject s 1 (n : WithTop ℕ)) =
      (truncatedUnderlyingComplex cm s₀ t).cycleSubobject s 1 (n : WithTop ℕ) := by
  apply filteredComplexMorphism_map_cycleSubobject_eq
    (unboundedUnderlyingComplexProjection cm s₀ t) s 1 n
    (unboundedUCAssocGradedProjectionIso cm s₀ t s 1 hs)
    (unboundedUCProjection_assocGradedMap_eq_iso_hom cm s₀ t s 1 hs)
  · rw [unboundedUCProjection_filtCompat_one]
    unfold Filtration.toTruncatedFiltration
    infer_instance
  · rw [unboundedUCProjection_cycleCokernelMap_one_eq
      cm s₀ t s n hcycle]
    infer_instance

/-- 若环境映射是满射、两个相关过滤层上的提升是满射，
且环境映射的核已落在当前过滤层中，则关联分次同构精确保持
相应的有限边缘层。 -/
private theorem filteredComplexMorphism_map_boundarySubobject_eq
    {X Y : FilteredComplex C} (g : FilteredComplexMorphism X Y)
    (s k : ℤ) (n : ℕ)
    (e : X.assocGraded s k ≅ Y.assocGraded s k)
    (he : g.assocGradedMap s k = e.hom)
    (_hp : Epi (g.f k))
    (hsource : Epi (g.filt_compat (s - (n : ℤ) + 1) (k + 1)).choose)
    (hcurrent : Epi (g.filt_compat s k).choose)
    (hker : kernelSubobject (g.f k) ≤ X.fil s k) :
    (Subobject.mapIsoToOrderIso e)
        (X.boundarySubobject s k (n : WithTop ℕ)) =
      Y.boundarySubobject s k (n : WithTop ℕ) := by
  let a : ℤ := s - (n : ℤ) + 1
  let p := g.f k
  let q := (g.filt_compat a (k + 1)).choose
  let u := (g.filt_compat s k).choose
  have hpq := (g.filt_compat a (k + 1)).choose_spec
  have hpu := (g.filt_compat s k).choose_spec
  have hd : g.f (k + 1) ≫ Y.dToK k = X.dToK k ≫ p := by
    let ek : k + 1 - 1 = k := by omega
    have ht : g.f (k + 1 - 1) ≫ eqToHom (congrArg Y.A ek) =
        eqToHom (congrArg X.A ek) ≫ g.f k :=
      eqToHom_naturality (fun j => g.f j) ek
    unfold FilteredComplex.dToK
    rw [← Category.assoc, g.comm_d (k + 1), Category.assoc, ht]
    simp only [Category.assoc, p]
  have hgen : q ≫ ((Y.fil a (k + 1)).arrow ≫ Y.dToK k) =
      ((X.fil a (k + 1)).arrow ≫ X.dToK k) ≫ p := by
    rw [← Category.assoc, hpq, Category.assoc, hd]
    simp only [Category.assoc]
  let JX := imageSubobject ((X.fil a (k + 1)).arrow ≫ X.dToK k)
  let JY := imageSubobject ((Y.fil a (k + 1)).arrow ≫ Y.dToK k)
  let IX := JX ⊓ X.fil s k
  let IY := JY ⊓ Y.fil s k
  let jMap := imageSubobjectMap (Arrow.homMk' q p hgen)
  have hj : jMap ≫ JY.arrow = JX.arrow ≫ p :=
    imageSubobjectMap_arrow _
  have hfacJ : JY.Factors (IX.arrow ≫ p) := by
    have hIX : JX.Factors IX.arrow := Subobject.inf_arrow_factors_left _ _
    rw [← Subobject.factorThru_arrow _ _ hIX, Category.assoc, ← hj]
    exact Subobject.factors_of_factors_right _ (Subobject.factors_comp_arrow _)
  have hfacF : (Y.fil s k).Factors (IX.arrow ≫ p) := by
    have hIX : (X.fil s k).Factors IX.arrow :=
      Subobject.inf_arrow_factors_right _ _
    rw [← Subobject.factorThru_arrow _ _ hIX, Category.assoc, ← hpu]
    exact Subobject.factors_of_factors_right _ (Subobject.factors_comp_arrow _)
  have hfacI : IY.Factors (IX.arrow ≫ p) := by
    rw [show IY = JY ⊓ Y.fil s k from rfl, Subobject.inf_factors]
    exact ⟨hfacJ, hfacF⟩
  let α := IY.factorThru (IX.arrow ≫ p) hfacI
  have hα : α ≫ IY.arrow = IX.arrow ≫ p :=
    IY.factorThru_arrow _ hfacI
  haveI : Epi p := _hp
  haveI : Epi q := hsource
  haveI : Epi u := hcurrent
  haveI : Epi jMap := by
    dsimp only [jMap]
    exact imageSubobjectMap_epi_of_epi_left q p hgen
  haveI : Epi α := by
    exact infLift_epi_of_epi_of_kernel_le p JX (X.fil s k)
      JY (Y.fil s k) jMap u hj hpu hker α hα
  let πX := X.filToAssocGraded s k
  let πY := Y.filToAssocGraded s k
  have hπ : u ≫ πY = πX ≫ e.hom := by
    rw [← he]
    unfold FilteredComplexMorphism.assocGradedMap πX πY
      FilteredComplex.filToAssocGraded
    exact (cokernel.π_desc _ _ _).symm
  let βX := Subobject.ofLE IX (X.fil s k) inf_le_right ≫ πX
  let βY := Subobject.ofLE IY (Y.fil s k) inf_le_right ≫ πY
  have hmid : α ≫ Subobject.ofLE IY (Y.fil s k) inf_le_right =
      Subobject.ofLE IX (X.fil s k) inf_le_right ≫ u := by
    apply (cancel_mono (Y.fil s k).arrow).1
    calc
      (α ≫ Subobject.ofLE IY (Y.fil s k) inf_le_right) ≫
          (Y.fil s k).arrow = α ≫ IY.arrow := by
        rw [Category.assoc, Subobject.ofLE_arrow]
      _ = IX.arrow ≫ p := hα
      _ = (Subobject.ofLE IX (X.fil s k) inf_le_right ≫ u) ≫
          (Y.fil s k).arrow := by
        rw [Category.assoc, hpu, ← Category.assoc, Subobject.ofLE_arrow]
  have hβ : α ≫ βY = βX ≫ e.hom := by
    simp only [βX, βY, ← Category.assoc]
    rw [hmid, Category.assoc, hπ]
    simp only [Category.assoc]
  have himage : imageSubobject (βX ≫ e.hom) = imageSubobject βY := by
    simpa only [hβ] using imageSubobject_epi_comp_eq α βY
  change (Subobject.map e.hom).obj (imageSubobject βX) =
    imageSubobject βY
  calc
    (Subobject.map e.hom).obj (imageSubobject βX) =
        imageSubobject (βX ≫ e.hom) := by
      rw [← Subobject.mk_arrow (imageSubobject βX), Subobject.map_mk,
        ← Subobject.mk_arrow (imageSubobject (βX ≫ e.hom))]
      exact Subobject.mk_eq_mk_of_comm _ _
        (imageSubobjectCompIso βX e.hom).symm
        (imageSubobjectCompIso_inv_arrow βX e.hom)
    _ = imageSubobject βY := himage

/-- 截断层覆盖当前关联分次时，规范投影精确地把次数 `0`
的未截断有限边缘层送到截断边缘层。 -/
private theorem unboundedUCProjection_map_boundarySubobject_zero_eq
    (cm : ConvergenceMorphism conv₁ conv₂) (s₀ : ℤ) (t : ω')
    (s : ℤ) (n : ℕ) (hs : s ≤ s₀) :
    (Subobject.mapIsoToOrderIso
      (unboundedUCAssocGradedProjectionIso cm s₀ t s 0 hs))
        ((unboundedUnderlyingComplex cm t).boundarySubobject s 0 (n : WithTop ℕ)) =
      (truncatedUnderlyingComplex cm s₀ t).boundarySubobject s 0
        (n : WithTop ℕ) := by
  apply filteredComplexMorphism_map_boundarySubobject_eq
    (unboundedUnderlyingComplexProjection cm s₀ t) s 0 n
    (unboundedUCAssocGradedProjectionIso cm s₀ t s 0 hs)
    (unboundedUCProjection_assocGradedMap_eq_iso_hom cm s₀ t s 0 hs)
  · rw [unboundedUCProjection_f_zero]
    unfold Filtration.truncationProj
    infer_instance
  · rw [show (0 : ℤ) + 1 = 1 by omega,
      unboundedUCProjection_filtCompat_one]
    unfold Filtration.toTruncatedFiltration
    infer_instance
  · rw [unboundedUCProjection_filtCompat_zero]
    unfold Filtration.toTruncatedFiltration
    infer_instance
  · rw [unboundedUCProjection_f_zero]
    change kernelSubobject (F₂.truncationProj s₀ t) ≤ F₂.F s t
    exact kernelSubobject_truncationProj_le F₂ s₀ s t (by omega)

/-- 同构下对应的子对象具有规范的底层对象同构。 -/
private noncomputable def subobjectUnderlyingIsoOfMapIsoEq
    [LocallySmall.{w₀} C] [WellPowered.{w₀} C]
    [HasWidePullbacks.{w₀} C] [HasCoproducts.{w₀} C]
    {X Y : C} (e : X ≅ Y) (P : Subobject X) (Q : Subobject Y)
    (h : (Subobject.mapIsoToOrderIso e) P = Q) : (P : C) ≅ (Q : C) := by
  have hfac : Q.Factors (P.arrow ≫ e.hom) :=
    subobject_factors_of_mapIso_eq e P Q h
  have hinv : (Subobject.mapIsoToOrderIso e.symm) Q = P := by
    let O := Subobject.mapIsoToOrderIso e
    change O.symm Q = P
    rw [← h, O.symm_apply_apply]
  have hfacInv : P.Factors (Q.arrow ≫ e.inv) :=
    subobject_factors_of_mapIso_eq e.symm Q P hinv
  let f := Q.factorThru (P.arrow ≫ e.hom) hfac
  let g := P.factorThru (Q.arrow ≫ e.inv) hfacInv
  refine
    { hom := f
      inv := g
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply (cancel_mono P.arrow).1
    dsimp only [f, g]
    rw [Category.assoc, P.factorThru_arrow, ← Category.assoc,
      Q.factorThru_arrow, Category.assoc, e.hom_inv_id,
      Category.comp_id, Category.id_comp]
  · apply (cancel_mono Q.arrow).1
    dsimp only [f, g]
    rw [Category.assoc, Q.factorThru_arrow, ← Category.assoc,
      P.factorThru_arrow, Category.assoc, e.inv_hom_id,
      Category.comp_id, Category.id_comp]

/-- 若一个环境同构同时精确保持有限边缘层和循环层，
则它诱导相应有限页的同构。 -/
private noncomputable def filteredComplexFinitePageIsoOfSubobjectEq
    [LocallySmall.{w₀} C] [WellPowered.{w₀} C]
    [HasWidePullbacks.{w₀} C] [HasCoproducts.{w₀} C]
    (X Y : FilteredComplex C) (s k : ℤ) (n : ℕ)
    (e : X.assocGraded s k ≅ Y.assocGraded s k)
    (hB : (Subobject.mapIsoToOrderIso e)
        (X.boundarySubobject s k (n : WithTop ℕ)) =
      Y.boundarySubobject s k (n : WithTop ℕ))
    (hZ : (Subobject.mapIsoToOrderIso e)
        (X.cycleSubobject s k (n : WithTop ℕ)) =
      Y.cycleSubobject s k (n : WithTop ℕ)) :
    X.finitePage s k n ≅ Y.finitePage s k n := by
  let BX := X.boundarySubobject s k (n : WithTop ℕ)
  let BY := Y.boundarySubobject s k (n : WithTop ℕ)
  let ZX := X.cycleSubobject s k (n : WithTop ℕ)
  let ZY := Y.cycleSubobject s k (n : WithTop ℕ)
  let eB := subobjectUnderlyingIsoOfMapIsoEq e BX BY hB
  let eZ := subobjectUnderlyingIsoOfMapIsoEq e ZX ZY hZ
  let iX := Subobject.ofLE BX ZX (X.B_le_Z_aux s k n)
  let iY := Subobject.ofLE BY ZY (Y.B_le_Z_aux s k n)
  have heB : eB.hom ≫ BY.arrow = BX.arrow ≫ e.hom := by
    dsimp only [eB, subobjectUnderlyingIsoOfMapIsoEq]
    exact BY.factorThru_arrow _
      (subobject_factors_of_mapIso_eq e BX BY hB)
  have heZ : eZ.hom ≫ ZY.arrow = ZX.arrow ≫ e.hom := by
    dsimp only [eZ, subobjectUnderlyingIsoOfMapIsoEq]
    exact ZY.factorThru_arrow _
      (subobject_factors_of_mapIso_eq e ZX ZY hZ)
  have hsquare : iX ≫ eZ.hom = eB.hom ≫ iY := by
    apply (cancel_mono ZY.arrow).1
    calc
      (iX ≫ eZ.hom) ≫ ZY.arrow = iX ≫ (eZ.hom ≫ ZY.arrow) :=
        Category.assoc _ _ _
      _ = iX ≫ ZX.arrow ≫ e.hom := by rw [heZ]
      _ = BX.arrow ≫ e.hom := by
        rw [← Category.assoc, show iX ≫ ZX.arrow = BX.arrow by
          exact Subobject.ofLE_arrow _]
      _ = eB.hom ≫ BY.arrow := heB.symm
      _ = (eB.hom ≫ iY) ≫ ZY.arrow := by
        rw [Category.assoc, show iY ≫ ZY.arrow = BY.arrow by
          exact Subobject.ofLE_arrow _]
  exact cokernel.mapIso iX iY eB eZ hsquare

/-- 过滤复形态射把任意有限循环层映入对应的有限循环层。这里不需要有界性。 -/
private theorem filteredComplexMorphism_cycleSubobject_preserved_nat
    {X Y : FilteredComplex C} (g : FilteredComplexMorphism X Y)
    (s k : ℤ) (n : ℕ) :
    ∃ (lift : Subobject.underlying.obj
          (X.cycleSubobject s k (n : WithTop ℕ)) ⟶
        Subobject.underlying.obj
          (Y.cycleSubobject s k (n : WithTop ℕ))),
      lift ≫ (Y.cycleSubobject s k (n : WithTop ℕ)).arrow =
        (X.cycleSubobject s k (n : WithTop ℕ)).arrow ≫
          g.assocGradedMap s k := by
  set u := (g.filt_compat s k).choose
  have hu := (g.filt_compat s k).choose_spec
  set πX := X.filToAssocGraded s k
  set πY := Y.filToAssocGraded s k
  have hπ : u ≫ πY = πX ≫ g.assocGradedMap s k := by
    unfold FilteredComplexMorphism.assocGradedMap πX πY
      FilteredComplex.filToAssocGraded
    exact (cokernel.π_desc _ _ _).symm
  set w := (g.filt_compat (s + ↑n) (k - 1)).choose
  have hw := (g.filt_compat (s + ↑n) (k - 1)).choose_spec
  set q := cokernel.map ((X.fil (s + ↑n) (k - 1)).arrow)
    ((Y.fil (s + ↑n) (k - 1)).arrow) w (g.f (k - 1)) hw.symm
  have hq : cokernel.π ((X.fil (s + ↑n) (k - 1)).arrow) ≫ q =
      g.f (k - 1) ≫
        cokernel.π ((Y.fil (s + ↑n) (k - 1)).arrow) := by
    unfold q
    exact cokernel.π_desc _ _ _
  have hsquare : u ≫
      ((Y.fil s k).arrow ≫ Y.d k ≫
        cokernel.π ((Y.fil (s + ↑n) (k - 1)).arrow)) =
    ((X.fil s k).arrow ≫ X.d k ≫
        cokernel.π ((X.fil (s + ↑n) (k - 1)).arrow)) ≫ q := by
    calc
      u ≫ (Y.fil s k).arrow ≫ Y.d k ≫
          cokernel.π ((Y.fil (s + ↑n) (k - 1)).arrow) =
        (X.fil s k).arrow ≫ g.f k ≫ Y.d k ≫
          cokernel.π ((Y.fil (s + ↑n) (k - 1)).arrow) := by
            rw [← Category.assoc, hu]
            simp only [Category.assoc]
      _ = (X.fil s k).arrow ≫ X.d k ≫ g.f (k - 1) ≫
          cokernel.π ((Y.fil (s + ↑n) (k - 1)).arrow) := by
            simpa only [Category.assoc] using congrArg
              (fun z => (X.fil s k).arrow ≫ z ≫
                cokernel.π ((Y.fil (s + ↑n) (k - 1)).arrow))
              (g.comm_d k)
      _ = (X.fil s k).arrow ≫ X.d k ≫
          cokernel.π ((X.fil (s + ↑n) (k - 1)).arrow) ≫ q := by
            rw [hq]
      _ = ((X.fil s k).arrow ≫ X.d k ≫
          cokernel.π ((X.fil (s + ↑n) (k - 1)).arrow)) ≫ q := by
            simp only [Category.assoc]
  change ∃ lift, lift ≫
      (imageSubobject
        ((kernelSubobject ((Y.fil s k).arrow ≫ Y.d k ≫
          cokernel.π ((Y.fil (s + ↑n) (k - 1)).arrow))).arrow ≫ πY)).arrow =
    (imageSubobject
      ((kernelSubobject ((X.fil s k).arrow ≫ X.d k ≫
        cokernel.π ((X.fil (s + ↑n) (k - 1)).arrow))).arrow ≫ πX)).arrow ≫
      g.assocGradedMap s k
  exact imageSubobjectMap_of_kernel_cokernel_square hsquare hπ

/-- 过滤复形态射把任意有限边缘层映入对应的有限边缘层。这里同样不需要有界性。 -/
private theorem filteredComplexMorphism_boundarySubobject_preserved_nat
    {X Y : FilteredComplex C} (g : FilteredComplexMorphism X Y)
    (s k : ℤ) (n : ℕ) :
    ∃ (lift : Subobject.underlying.obj
          (X.boundarySubobject s k (n : WithTop ℕ)) ⟶
        Subobject.underlying.obj
          (Y.boundarySubobject s k (n : WithTop ℕ))),
      lift ≫ (Y.boundarySubobject s k (n : WithTop ℕ)).arrow =
        (X.boundarySubobject s k (n : WithTop ℕ)).arrow ≫
          g.assocGradedMap s k := by
  set u := (g.filt_compat s k).choose
  have hu := (g.filt_compat s k).choose_spec
  set πX := X.filToAssocGraded s k
  set πY := Y.filToAssocGraded s k
  have hπ : u ≫ πY = πX ≫ g.assocGradedMap s k := by
    unfold FilteredComplexMorphism.assocGradedMap πX πY
      FilteredComplex.filToAssocGraded
    exact (cokernel.π_desc _ _ _).symm
  have hd : g.f (k + 1) ≫ Y.dToK k = X.dToK k ≫ g.f k := by
    let e : k + 1 - 1 = k := by omega
    have ht : g.f (k + 1 - 1) ≫ eqToHom (congrArg Y.A e) =
        eqToHom (congrArg X.A e) ≫ g.f k :=
      eqToHom_naturality (fun j => g.f j) e
    unfold FilteredComplex.dToK
    rw [← Category.assoc, g.comm_d (k + 1), Category.assoc, ht]
    simp only [Category.assoc]
  let a : ℤ := s - (n : ℤ) + 1
  let q := (g.filt_compat a (k + 1)).choose
  have hq := (g.filt_compat a (k + 1)).choose_spec
  have hgen : q ≫ ((Y.fil a (k + 1)).arrow ≫ Y.dToK k) =
      ((X.fil a (k + 1)).arrow ≫ X.dToK k) ≫ g.f k := by
    rw [← Category.assoc, hq, Category.assoc, hd]
    simp only [Category.assoc]
  let imgX := imageSubobject ((X.fil a (k + 1)).arrow ≫ X.dToK k)
  let imgY := imageSubobject ((Y.fil a (k + 1)).arrow ≫ Y.dToK k)
  let IX := imgX ⊓ X.fil s k
  let IY := imgY ⊓ Y.fil s k
  let imgMap := imageSubobjectMap (Arrow.homMk' q (g.f k) hgen)
  have himg : imgMap ≫ imgY.arrow = imgX.arrow ≫ g.f k :=
    imageSubobjectMap_arrow _
  have hfacImg : imgY.Factors (IX.arrow ≫ g.f k) := by
    have hIX : imgX.Factors IX.arrow :=
      Subobject.inf_arrow_factors_left _ _
    rw [← Subobject.factorThru_arrow _ _ hIX, Category.assoc, ← himg]
    exact Subobject.factors_of_factors_right _ (Subobject.factors_comp_arrow _)
  have hfacFil : (Y.fil s k).Factors (IX.arrow ≫ g.f k) := by
    have hIX : (X.fil s k).Factors IX.arrow :=
      Subobject.inf_arrow_factors_right _ _
    rw [← Subobject.factorThru_arrow _ _ hIX, Category.assoc, ← hu]
    exact Subobject.factors_of_factors_right _ (Subobject.factors_comp_arrow _)
  have hfacI : IY.Factors (IX.arrow ≫ g.f k) := by
    rw [show IY = imgY ⊓ Y.fil s k from rfl, Subobject.inf_factors]
    exact ⟨hfacImg, hfacFil⟩
  let α := IY.factorThru (IX.arrow ≫ g.f k) hfacI
  have hα : α ≫ IY.arrow = IX.arrow ≫ g.f k :=
    IY.factorThru_arrow _ hfacI
  have hmid : α ≫ Subobject.ofLE IY (Y.fil s k) inf_le_right =
      Subobject.ofLE IX (X.fil s k) inf_le_right ≫ u := by
    apply (cancel_mono (Y.fil s k).arrow).1
    calc
      (α ≫ Subobject.ofLE IY (Y.fil s k) inf_le_right) ≫
          (Y.fil s k).arrow = α ≫ IY.arrow := by
            rw [Category.assoc, Subobject.ofLE_arrow]
      _ = IX.arrow ≫ g.f k := hα
      _ = (Subobject.ofLE IX (X.fil s k) inf_le_right ≫ u) ≫
          (Y.fil s k).arrow := by
            rw [Category.assoc, hu, ← Category.assoc, Subobject.ofLE_arrow]
  have hsquare : α ≫
      (Subobject.ofLE IY (Y.fil s k) inf_le_right ≫ πY) =
    (Subobject.ofLE IX (X.fil s k) inf_le_right ≫ πX) ≫
      g.assocGradedMap s k := by
    rw [← Category.assoc, hmid, Category.assoc, hπ]
    simp only [Category.assoc]
  change ∃ lift, lift ≫
      (imageSubobject
        (Subobject.ofLE IY (Y.fil s k) inf_le_right ≫ πY)).arrow =
    (imageSubobject
      (Subobject.ofLE IX (X.fil s k) inf_le_right ≫ πX)).arrow ≫
      g.assocGradedMap s k
  exact ⟨imageSubobjectMap (Arrow.homMk' α (g.assocGradedMap s k) hsquare),
    imageSubobjectMap_arrow _⟩

/-- 过滤复形态射在有限页上的规范商映射；构造只依赖有限 `Z/B` 层。 -/
private noncomputable def filteredComplexMorphismFinitePageMap
    {X Y : FilteredComplex C} (g : FilteredComplexMorphism X Y)
    (s k : ℤ) (n : ℕ) :
    X.finitePage s k n ⟶ Y.finitePage s k n :=
  cokernel.map
    (Subobject.ofLE (X.boundarySubobject s k (n : WithTop ℕ))
      (X.cycleSubobject s k (n : WithTop ℕ)) (X.B_le_Z_aux s k n))
    (Subobject.ofLE (Y.boundarySubobject s k (n : WithTop ℕ))
      (Y.cycleSubobject s k (n : WithTop ℕ)) (Y.B_le_Z_aux s k n))
    (filteredComplexMorphism_boundarySubobject_preserved_nat g s k n).choose
    (filteredComplexMorphism_cycleSubobject_preserved_nat g s k n).choose
    (by
      apply (cancel_mono
        (Y.cycleSubobject s k (n : WithTop ℕ)).arrow).1
      simp only [Category.assoc,
        (filteredComplexMorphism_cycleSubobject_preserved_nat g s k n).choose_spec,
        Subobject.ofLE_arrow,
        (filteredComplexMorphism_boundarySubobject_preserved_nat g s k n).choose_spec,
        Subobject.ofLE_arrow_assoc])

/-- 有限页规范映射与循环层到页的商投影交换。 -/
private theorem filteredComplexMorphism_finitePageπ_naturality
    {X Y : FilteredComplex C} (g : FilteredComplexMorphism X Y)
    (s k : ℤ) (n : ℕ) :
    X.finitePageπ s k n ≫ filteredComplexMorphismFinitePageMap g s k n =
      (filteredComplexMorphism_cycleSubobject_preserved_nat g s k n).choose ≫
        Y.finitePageπ s k n := by
  simp [filteredComplexMorphismFinitePageMap, FilteredComplex.finitePageπ]

private theorem truncatedUC_cycleSubobject_one_preserved
    (cm : ConvergenceMorphism conv₁ conv₂)
    (_hbb₁ : F₁.IsBoundedBelow) (_hbb₂ : F₂.IsBoundedBelow)
    {s₀ s₁ : ℤ} (h : s₀ ≤ s₁) (t : ω') (s : ℤ) (r : WithTop ℕ) :
    ∃ (lift : Subobject.underlying.obj
          ((truncatedUnderlyingComplex cm s₁ t).cycleSubobject s 1 r) ⟶
        Subobject.underlying.obj
          ((truncatedUnderlyingComplex cm s₀ t).cycleSubobject s 1 r)),
      lift ≫ ((truncatedUnderlyingComplex cm s₀ t).cycleSubobject s 1 r).arrow =
        ((truncatedUnderlyingComplex cm s₁ t).cycleSubobject s 1 r).arrow ≫
          (eqToHom (truncatedUC_assocGraded_one cm s₁ t s) ≫
            Filtration.inducedAssocGradedMap
              (fun k' => F₁.truncationTransition h k')
              (fun s' k' => truncationTransition_fil_compat₁ h s' k')
              s t ≫
            eqToHom (truncatedUC_assocGraded_one cm s₀ t s).symm) := by
  set grφ := eqToHom (truncatedUC_assocGraded_one cm s₁ t s) ≫
            Filtration.inducedAssocGradedMap
              (fun k' => F₁.truncationTransition h k')
              (fun s' k' => truncationTransition_fil_compat₁ h s' k')
              s t ≫
            eqToHom (truncatedUC_assocGraded_one cm s₀ t s).symm with hgrφ_def
  set compat_s := (truncationTransition_fil_compat₁ (F₁ := F₁) h s t).choose
  have hcompat_s := (truncationTransition_fil_compat₁ (F₁ := F₁) h s t).choose_spec
  have h_d_square : compat_s ≫
      (((truncatedUnderlyingComplex cm s₀ t).fil s 1).arrow ≫
        (truncatedUnderlyingComplex cm s₀ t).d 1) =
      (((truncatedUnderlyingComplex cm s₁ t).fil s 1).arrow ≫
        (truncatedUnderlyingComplex cm s₁ t).d 1) ≫
      F₂.truncationTransition h t := by
    simp only [truncatedUnderlyingComplex, underlyingComplex, twoTermDiff, twoTermFil,
      ↓reduceDIte, eqToHom_refl, Category.id_comp, Category.comp_id]
    simp only [Category.assoc]
    show compat_s ≫ ((F₁.truncatedFiltration s₀).F s t).arrow ≫
        cm.truncatedAMap s₀ t =
      ((F₁.truncatedFiltration s₁).F s t).arrow ≫
        cm.truncatedAMap s₁ t ≫ F₂.truncationTransition h t
    rw [← truncatedAMap_naturality cm h t, ← Category.assoc,
      ← Category.assoc, hcompat_s, Category.assoc]
  delta FilteredComplex.cycleSubobject
  dsimp only []
  cases r with
  | top =>
    have h_grφ_simp : grφ =
        Filtration.inducedAssocGradedMap
          (fun k' => F₁.truncationTransition h k')
          (fun s' k' => truncationTransition_fil_compat₁ h s' k')
          s t := by
      simp only [grφ, truncatedUnderlyingComplex, underlyingComplex,
        FilteredComplex.assocGraded, Filtration.associatedGraded, twoTermFil]
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    have h_πV_comm : compat_s ≫
        cokernel.π (Subobject.ofLE
          ((truncatedUnderlyingComplex cm s₀ t).fil (s + 1) 1)
          ((truncatedUnderlyingComplex cm s₀ t).fil s 1)
          (FilteredComplex.fil_anti (truncatedUnderlyingComplex cm s₀ t) s 1)) =
        cokernel.π (Subobject.ofLE
          ((truncatedUnderlyingComplex cm s₁ t).fil (s + 1) 1)
          ((truncatedUnderlyingComplex cm s₁ t).fil s 1)
          (FilteredComplex.fil_anti (truncatedUnderlyingComplex cm s₁ t) s 1)) ≫ grφ := by
      rw [h_grφ_simp]
      change compat_s ≫
          cokernel.π (Subobject.ofLE ((F₁.truncatedFiltration s₀).F (s + 1) t)
            ((F₁.truncatedFiltration s₀).F s t)
            ((F₁.truncatedFiltration s₀).mono s t)) =
        cokernel.π (Subobject.ofLE ((F₁.truncatedFiltration s₁).F (s + 1) t)
            ((F₁.truncatedFiltration s₁).F s t)
            ((F₁.truncatedFiltration s₁).mono s t)) ≫
          Filtration.inducedAssocGradedMap
            (fun k' => F₁.truncationTransition h k')
            (fun s' k' => truncationTransition_fil_compat₁ h s' k')
            s t
      simp only [Filtration.inducedAssocGradedMap]
      rw [cokernel.π_desc]
    exact imageSubobjectMap_of_kernel_cokernel_square h_d_square h_πV_comm
  | coe n =>
    -- grφ simplification: strip eqToHom wrappers
    have h_grφ_simp : grφ =
        Filtration.inducedAssocGradedMap
          (fun k' => F₁.truncationTransition h k')
          (fun s' k' => truncationTransition_fil_compat₁ h s' k')
          s t := by
      simp only [grφ, truncatedUnderlyingComplex, underlyingComplex,
        FilteredComplex.assocGraded, Filtration.associatedGraded, twoTermFil]
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    -- πV commutativity in truncatedUnderlyingComplex terms (matching goal shape)
    have h_πV_comm : compat_s ≫
        cokernel.π (Subobject.ofLE
          ((truncatedUnderlyingComplex cm s₀ t).fil (s + 1) 1)
          ((truncatedUnderlyingComplex cm s₀ t).fil s 1)
          (FilteredComplex.fil_anti (truncatedUnderlyingComplex cm s₀ t) s 1)) =
        cokernel.π (Subobject.ofLE
          ((truncatedUnderlyingComplex cm s₁ t).fil (s + 1) 1)
          ((truncatedUnderlyingComplex cm s₁ t).fil s 1)
          (FilteredComplex.fil_anti (truncatedUnderlyingComplex cm s₁ t) s 1)) ≫ grφ := by
      rw [h_grφ_simp]
      change compat_s ≫
          cokernel.π (Subobject.ofLE ((F₁.truncatedFiltration s₀).F (s + 1) t)
            ((F₁.truncatedFiltration s₀).F s t)
            ((F₁.truncatedFiltration s₀).mono s t)) =
        cokernel.π (Subobject.ofLE ((F₁.truncatedFiltration s₁).F (s + 1) t)
            ((F₁.truncatedFiltration s₁).F s t)
            ((F₁.truncatedFiltration s₁).mono s t)) ≫
          Filtration.inducedAssocGradedMap
            (fun k' => F₁.truncationTransition h k')
            (fun s' k' => truncationTransition_fil_compat₁ h s' k')
            s t
      simp only [Filtration.inducedAssocGradedMap]
      rw [cokernel.π_desc]
    -- Build the cokernel map on the right side, in truncatedUnderlyingComplex terms
    obtain ⟨φ_sn, hφ_sn⟩ := truncationTransition_fil_compat₂ (F₂ := F₂) h (s + ↑n) t
    have h_cok_cond : ((truncatedUnderlyingComplex cm s₁ t).fil (s + ↑n) (1 - 1)).arrow ≫
        (F₂.truncationTransition h t ≫
          cokernel.π ((truncatedUnderlyingComplex cm s₀ t).fil (s + ↑n) (1 - 1)).arrow) = 0 := by
      show ((F₂.truncatedFiltration s₁).F (s + ↑n) t).arrow ≫
        (F₂.truncationTransition h t ≫
          cokernel.π ((F₂.truncatedFiltration s₀).F (s + ↑n) t).arrow) = 0
      rw [← Category.assoc, ← hφ_sn, Category.assoc, cokernel.condition, comp_zero]
    let cok_right := cokernel.desc
      ((truncatedUnderlyingComplex cm s₁ t).fil (s + ↑n) (1 - 1)).arrow
      (F₂.truncationTransition h t ≫
        cokernel.π ((truncatedUnderlyingComplex cm s₀ t).fil (s + ↑n) (1 - 1)).arrow)
      h_cok_cond
    have h_cok_π : cokernel.π ((truncatedUnderlyingComplex cm s₁ t).fil (s + ↑n) (1 - 1)).arrow ≫
        cok_right = F₂.truncationTransition h t ≫
        cokernel.π ((truncatedUnderlyingComplex cm s₀ t).fil (s + ↑n) (1 - 1)).arrow :=
      cokernel.π_desc _ _ _
    -- Kernel square in truncatedUnderlyingComplex terms
    have h_ker_sq : compat_s ≫
        (((truncatedUnderlyingComplex cm s₀ t).fil s 1).arrow ≫
          (truncatedUnderlyingComplex cm s₀ t).d 1 ≫
          cokernel.π ((truncatedUnderlyingComplex cm s₀ t).fil (s + ↑n) (1 - 1)).arrow) =
        (((truncatedUnderlyingComplex cm s₁ t).fil s 1).arrow ≫
          (truncatedUnderlyingComplex cm s₁ t).d 1 ≫
          cokernel.π ((truncatedUnderlyingComplex cm s₁ t).fil (s + ↑n) (1 - 1)).arrow) ≫
        cok_right := by
      calc
        _ = (compat_s ≫
              (((truncatedUnderlyingComplex cm s₀ t).fil s 1).arrow ≫
                (truncatedUnderlyingComplex cm s₀ t).d 1)) ≫
              cokernel.π
                ((truncatedUnderlyingComplex cm s₀ t).fil (s + ↑n) (1 - 1)).arrow := by
            simp only [Category.assoc]
        _ = ((((truncatedUnderlyingComplex cm s₁ t).fil s 1).arrow ≫
                (truncatedUnderlyingComplex cm s₁ t).d 1) ≫
              F₂.truncationTransition h t) ≫
              cokernel.π
                ((truncatedUnderlyingComplex cm s₀ t).fil (s + ↑n) (1 - 1)).arrow := by
            rw [h_d_square]
        _ = (((truncatedUnderlyingComplex cm s₁ t).fil s 1).arrow ≫
              (truncatedUnderlyingComplex cm s₁ t).d 1) ≫
              (cokernel.π
                ((truncatedUnderlyingComplex cm s₁ t).fil (s + ↑n) (1 - 1)).arrow ≫
                cok_right) := by
            simp only [Category.assoc, h_cok_π]
        _ = _ := by simp only [Category.assoc]
    exact imageSubobjectMap_of_kernel_cokernel_square h_ker_sq h_πV_comm

private lemma factor_through_inf {X Y : C} {P Q : Subobject Y}
    (f : X ⟶ Y)
    (hP : P.Factors f) (hQ : Q.Factors f) :
    (P ⊓ Q).Factors f := by
  rw [Subobject.inf_factors]; exact ⟨hP, hQ⟩

private theorem truncatedUC_boundarySubobject_zero_preserved
    (cm : ConvergenceMorphism conv₁ conv₂)
    (hbb₁ : F₁.IsBoundedBelow) (hbb₂ : F₂.IsBoundedBelow)
    {s₀ s₁ : ℤ} (h : s₀ ≤ s₁) (t : ω') (s : ℤ) (r : WithTop ℕ) :
    ∃ (lift : Subobject.underlying.obj
          ((truncatedUnderlyingComplex cm s₁ t).boundarySubobject s 0 r) ⟶
        Subobject.underlying.obj
          ((truncatedUnderlyingComplex cm s₀ t).boundarySubobject s 0 r)),
      lift ≫ ((truncatedUnderlyingComplex cm s₀ t).boundarySubobject s 0 r).arrow =
        ((truncatedUnderlyingComplex cm s₁ t).boundarySubobject s 0 r).arrow ≫
          (eqToHom (truncatedUC_assocGraded_zero cm s₁ t s) ≫
            Filtration.inducedAssocGradedMap
              (fun k' => F₂.truncationTransition h k')
              (fun s' k' => truncationTransition_fil_compat₂ h s' k')
              s t ≫
            eqToHom (truncatedUC_assocGraded_zero cm s₀ t s).symm) := by
  -- Abbreviation for the graded map φ
  set grφ := eqToHom (truncatedUC_assocGraded_zero cm s₁ t s) ≫
    Filtration.inducedAssocGradedMap
      (fun k' => F₂.truncationTransition h k')
      (fun s' k' => truncationTransition_fil_compat₂ h s' k')
      s t ≫
    eqToHom (truncatedUC_assocGraded_zero cm s₀ t s).symm with hgrφ_def
  -- Strip eqToHom wrappers from grφ (must be BEFORE set FC₀/FC₁)
  have h_grφ_simp : grφ =
      Filtration.inducedAssocGradedMap
        (fun k' => F₂.truncationTransition h k')
        (fun s' k' => truncationTransition_fil_compat₂ h s' k')
        s t := by
    simp only [grφ, truncatedUnderlyingComplex, underlyingComplex,
      FilteredComplex.assocGraded, Filtration.associatedGraded, twoTermFil]
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  -- The filtration compat lift at s (for the cokernel = assocGraded)
  -- Use .choose so it matches what inducedAssocGradedMap uses internally
  set lift_s := (truncationTransition_fil_compat₂ (F₂ := F₂) h s t).choose
  have hlift_s_spec := (truncationTransition_fil_compat₂ (F₂ := F₂) h s t).choose_spec
  -- Naturality of dToK 0 w.r.t. the truncation transition
  have h_dToK_nat : F₁.truncationTransition h t ≫
      (truncatedUnderlyingComplex cm s₀ t).dToK 0 =
      (truncatedUnderlyingComplex cm s₁ t).dToK 0 ≫
        F₂.truncationTransition h t := by
    simp only [FilteredComplex.dToK, truncatedUnderlyingComplex,
      underlyingComplex, twoTermDiff, twoTermObj]
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    exact truncatedAMap_naturality cm h t
  -- Abbreviate the filtered complexes (use let, not set, to preserve grφ as let-binding)
  let FC₀ := truncatedUnderlyingComplex cm s₀ t
  let FC₁ := truncatedUnderlyingComplex cm s₁ t
  -- Case split on r
  cases r with
  | top =>
    set I₀ := imageSubobject (FC₀.dToK 0) ⊓ FC₀.fil s 0
    set I₁ := imageSubobject (FC₁.dToK 0) ⊓ FC₁.fil s 0
    -- Step 1: Prove I₀.Factors (I₁.arrow ≫ τ₂) using factorThru (not ofLE)
    -- For the imageSubobject factor:
    have h_fac_imgD₁ : (imageSubobject (FC₁.dToK 0)).Factors I₁.arrow :=
      Subobject.inf_arrow_factors_left _ _
    have h_imgD_map := imageSubobjectMap_arrow
      (Arrow.homMk' (F₁.truncationTransition h t)
        (F₂.truncationTransition h t) h_dToK_nat)
    have h_fac_imgD₀ : (imageSubobject (FC₀.dToK 0)).Factors
        (I₁.arrow ≫ F₂.truncationTransition h t) := by
      -- Rewrite I₁.arrow as factorThru ≫ imgD₁.arrow
      rw [← Subobject.factorThru_arrow _ _ h_fac_imgD₁, Category.assoc]
      -- Now goal: imgD₀.Factors (factorThru ≫ imgD₁.arrow ≫ τ₂)
      -- Use h_imgD_map: imgMap ≫ imgD₀.arrow = imgD₁.arrow ≫ Arrow.homMk'(...).right
      -- Arrow.homMk'(...).right = τ₂
      simp only [Arrow.homMk'] at h_imgD_map
      rw [← h_imgD_map]
      exact Subobject.factors_of_factors_right _ (Subobject.factors_comp_arrow _)
    -- For the filtration factor:
    have h_fac_fil₁ : (FC₁.fil s 0).Factors I₁.arrow :=
      Subobject.inf_arrow_factors_right _ _
    have h_fac_fil₀ : (FC₀.fil s 0).Factors
        (I₁.arrow ≫ F₂.truncationTransition h t) := by
      rw [← Subobject.factorThru_arrow _ _ h_fac_fil₁, Category.assoc]
      show (FC₀.fil s 0).Factors
          ((FC₁.fil s 0).factorThru I₁.arrow h_fac_fil₁ ≫
            ((F₂.truncatedFiltration s₁).F s t).arrow ≫ F₂.truncationTransition h t)
      rw [← hlift_s_spec]
      exact Subobject.factors_of_factors_right _ (Subobject.factors_comp_arrow _)
    have h_fac_I : I₀.Factors (I₁.arrow ≫ F₂.truncationTransition h t) :=
      factor_through_inf _ h_fac_imgD₀ h_fac_fil₀
    -- Step 2: Build α
    set α := I₀.factorThru _ h_fac_I
    have hα := I₀.factorThru_arrow _ h_fac_I
    -- Step 3: Prove the comm square for the boundary map
    -- boundarySubobject uses ofLE I (FC.fil s 0) inf_le_right ≫ cokernel.π ι
    set ι₀ := Subobject.ofLE (FC₀.fil (s + 1) 0) (FC₀.fil s 0) (FC₀.fil_anti s 0)
    set ι₁ := Subobject.ofLE (FC₁.fil (s + 1) 0) (FC₁.fil s 0) (FC₁.fil_anti s 0)
    have h_sq_comm : α ≫ (Subobject.ofLE I₀ (FC₀.fil s 0) inf_le_right ≫ cokernel.π ι₀) =
        (Subobject.ofLE I₁ (FC₁.fil s 0) inf_le_right ≫ cokernel.π ι₁) ≫ grφ := by
      -- Use cancel_mono to reduce to an equation about arrows
      -- First, rewrite ofLE ≫ arrow = arrow
      have h_ofLE₀ := Subobject.ofLE_arrow (X := I₀) (Y := FC₀.fil s 0) inf_le_right
      have h_ofLE₁ := Subobject.ofLE_arrow (X := I₁) (Y := FC₁.fil s 0) inf_le_right
      -- We need: α ≫ ofLE ≫ πV = ofLE ≫ πV ≫ grφ
      -- Strategy: show both sides, after composing with (FC₀.fil s 0).arrow, are equal,
      -- then use the cokernel exactness to conclude.
      -- Actually, let's use the known equation:
      -- h_lift_πV (after establishing it): lift_s ≫ πV₀ = πV₁ ≫ grφ
      -- And: α ≫ ofLE₀ ≫ (FC₀.fil s 0).arrow = α ≫ I₀.arrow (by ofLE_arrow)
      --     = I₁.arrow ≫ τ₂ (by hα)
      --     = ofLE₁ ≫ (FC₁.fil s 0).arrow ≫ τ₂ (by ofLE_arrow)
      --     = ofLE₁ ≫ lift_s ≫ (FC₀.fil s 0).arrow (by hlift_s_spec.symm... type issue)
      -- This shows: α ≫ ofLE₀ = ofLE₁ ≫ lift_s (after cancel_mono)
      -- Then: α ≫ ofLE₀ ≫ πV₀ = ofLE₁ ≫ lift_s ≫ πV₀ = ofLE₁ ≫ πV₁ ≫ grφ
      -- Intermediate: α ≫ ofLE₀ = ofLE₁ ≫ lift_s
      have hlift_FC : lift_s ≫ (FC₀.fil s 0).arrow =
          (FC₁.fil s 0).arrow ≫ F₂.truncationTransition h t := hlift_s_spec
      have h_mid : α ≫ Subobject.ofLE I₀ (FC₀.fil s 0) inf_le_right =
          Subobject.ofLE I₁ (FC₁.fil s 0) inf_le_right ≫ lift_s := by
        apply (cancel_mono (FC₀.fil s 0).arrow).mp
        simp only [Category.assoc]
        rw [h_ofLE₀, hα, hlift_FC, ← Category.assoc, h_ofLE₁]
      rw [← Category.assoc, h_mid, Category.assoc]
      -- Now goal: ofLE₁ ≫ lift_s ≫ πV₀ = (ofLE₁ ≫ πV₁) ≫ grφ
      rw [Category.assoc]
      congr 1
      -- Goal: lift_s ≫ πV₀ = πV₁ ≫ grφ
      -- This needs h_lift_πV, but we need to match types.
      -- πV₀ = cokernel.π ι₀ where ι₀ uses FC₀ types
      -- h_lift_πV needs πV with truncatedFiltration types
      -- Use show/change to normalize
      show lift_s ≫ cokernel.π (Subobject.ofLE
            ((F₂.truncatedFiltration s₀).F (s + 1) t)
            ((F₂.truncatedFiltration s₀).F s t)
            ((F₂.truncatedFiltration s₀).mono s t)) =
          cokernel.π (Subobject.ofLE
            ((F₂.truncatedFiltration s₁).F (s + 1) t)
            ((F₂.truncatedFiltration s₁).F s t)
            ((F₂.truncatedFiltration s₁).mono s t)) ≫ grφ
      rw [h_grφ_simp]
      simp only [Filtration.inducedAssocGradedMap]
      rw [cokernel.π_desc]
    -- Step 4: Conclude
    delta FilteredComplex.boundarySubobject
    exact ⟨imageSubobjectMap (Arrow.homMk' α grφ h_sq_comm),
           imageSubobjectMap_arrow (Arrow.homMk' α grφ h_sq_comm)⟩
  | coe n =>
    let q : ℤ := s - ↑n + 1
    set lift_q := (truncationTransition_fil_compat₁ (F₁ := F₁) h q t).choose
    have hlift_q_spec :=
      (truncationTransition_fil_compat₁ (F₁ := F₁) h q t).choose_spec
    have h_restricted_nat :
        lift_q ≫ (((truncatedUnderlyingComplex cm s₀ t).fil q 1).arrow ≫
          (truncatedUnderlyingComplex cm s₀ t).dToK 0) =
          (((truncatedUnderlyingComplex cm s₁ t).fil q 1).arrow ≫
            (truncatedUnderlyingComplex cm s₁ t).dToK 0) ≫
            F₂.truncationTransition h t := by
      simp only [FilteredComplex.dToK, truncatedUnderlyingComplex, underlyingComplex,
        twoTermDiff, twoTermFil, twoTermObj, zero_add, ↓reduceDIte,
        eqToHom_refl, Category.id_comp, Category.comp_id]
      simp only [Category.assoc]
      show lift_q ≫ ((F₁.truncatedFiltration s₀).F q t).arrow ≫
          cm.truncatedAMap s₀ t =
        ((F₁.truncatedFiltration s₁).F q t).arrow ≫
          cm.truncatedAMap s₁ t ≫ F₂.truncationTransition h t
      rw [← truncatedAMap_naturality cm h t, ← Category.assoc,
        ← Category.assoc, hlift_q_spec, Category.assoc]
    set I₀ := imageSubobject ((FC₀.fil q 1).arrow ≫ FC₀.dToK 0) ⊓ FC₀.fil s 0
    set I₁ := imageSubobject ((FC₁.fil q 1).arrow ≫ FC₁.dToK 0) ⊓ FC₁.fil s 0
    have h_fac_imgD₁ :
        (imageSubobject ((FC₁.fil q 1).arrow ≫ FC₁.dToK 0)).Factors I₁.arrow :=
      Subobject.inf_arrow_factors_left _ _
    have h_imgD_map := imageSubobjectMap_arrow
      (Arrow.homMk' lift_q (F₂.truncationTransition h t) h_restricted_nat)
    have h_fac_imgD₀ :
        (imageSubobject ((FC₀.fil q 1).arrow ≫ FC₀.dToK 0)).Factors
          (I₁.arrow ≫ F₂.truncationTransition h t) := by
      rw [← Subobject.factorThru_arrow _ _ h_fac_imgD₁, Category.assoc]
      simp only [Arrow.homMk'] at h_imgD_map
      rw [← h_imgD_map]
      exact Subobject.factors_of_factors_right _ (Subobject.factors_comp_arrow _)
    have h_fac_fil₁ : (FC₁.fil s 0).Factors I₁.arrow :=
      Subobject.inf_arrow_factors_right _ _
    have h_fac_fil₀ : (FC₀.fil s 0).Factors
        (I₁.arrow ≫ F₂.truncationTransition h t) := by
      rw [← Subobject.factorThru_arrow _ _ h_fac_fil₁, Category.assoc]
      show (FC₀.fil s 0).Factors
          ((FC₁.fil s 0).factorThru I₁.arrow h_fac_fil₁ ≫
            ((F₂.truncatedFiltration s₁).F s t).arrow ≫
              F₂.truncationTransition h t)
      rw [← hlift_s_spec]
      exact Subobject.factors_of_factors_right _ (Subobject.factors_comp_arrow _)
    have h_fac_I : I₀.Factors (I₁.arrow ≫ F₂.truncationTransition h t) :=
      factor_through_inf _ h_fac_imgD₀ h_fac_fil₀
    set α := I₀.factorThru _ h_fac_I
    have hα := I₀.factorThru_arrow _ h_fac_I
    set ι₀ := Subobject.ofLE (FC₀.fil (s + 1) 0) (FC₀.fil s 0) (FC₀.fil_anti s 0)
    set ι₁ := Subobject.ofLE (FC₁.fil (s + 1) 0) (FC₁.fil s 0) (FC₁.fil_anti s 0)
    have h_sq_comm :
        α ≫ (Subobject.ofLE I₀ (FC₀.fil s 0) inf_le_right ≫ cokernel.π ι₀) =
          (Subobject.ofLE I₁ (FC₁.fil s 0) inf_le_right ≫ cokernel.π ι₁) ≫ grφ := by
      have h_ofLE₀ := Subobject.ofLE_arrow (X := I₀) (Y := FC₀.fil s 0) inf_le_right
      have h_ofLE₁ := Subobject.ofLE_arrow (X := I₁) (Y := FC₁.fil s 0) inf_le_right
      have hlift_FC : lift_s ≫ (FC₀.fil s 0).arrow =
          (FC₁.fil s 0).arrow ≫ F₂.truncationTransition h t := hlift_s_spec
      have h_mid : α ≫ Subobject.ofLE I₀ (FC₀.fil s 0) inf_le_right =
          Subobject.ofLE I₁ (FC₁.fil s 0) inf_le_right ≫ lift_s := by
        apply (cancel_mono (FC₀.fil s 0).arrow).mp
        simp only [Category.assoc]
        rw [h_ofLE₀, hα, hlift_FC, ← Category.assoc, h_ofLE₁]
      rw [← Category.assoc, h_mid, Category.assoc, Category.assoc]
      congr 1
      show lift_s ≫ cokernel.π (Subobject.ofLE
            ((F₂.truncatedFiltration s₀).F (s + 1) t)
            ((F₂.truncatedFiltration s₀).F s t)
            ((F₂.truncatedFiltration s₀).mono s t)) =
          cokernel.π (Subobject.ofLE
            ((F₂.truncatedFiltration s₁).F (s + 1) t)
            ((F₂.truncatedFiltration s₁).F s t)
            ((F₂.truncatedFiltration s₁).mono s t)) ≫ grφ
      rw [h_grφ_simp]
      simp only [Filtration.inducedAssocGradedMap]
      rw [cokernel.π_desc]
    delta FilteredComplex.boundarySubobject
    change ∃ lift, lift ≫
        (imageSubobject
          (Subobject.ofLE I₀ (FC₀.fil s 0) inf_le_right ≫ cokernel.π ι₀)).arrow =
      (imageSubobject
          (Subobject.ofLE I₁ (FC₁.fil s 0) inf_le_right ≫ cokernel.π ι₁)).arrow ≫ grφ
    exact ⟨imageSubobjectMap (Arrow.homMk' α grφ h_sq_comm),
      imageSubobjectMap_arrow (Arrow.homMk' α grφ h_sq_comm)⟩

/-- 截断投影在两项过滤复形之间给出过滤复形态射。
    次数 `1` 和 `0` 的分量分别是 `F₁` 和 `F₂` 的截断转移；
    链映射条件正是 `truncatedAMap_naturality`。 -/
noncomputable def truncatedUnderlyingComplexTransition
    (cm : ConvergenceMorphism conv₁ conv₂)
    {s₀ s₁ : ℤ} (h : s₀ ≤ s₁) (t : ω') :
    FilteredComplexMorphism (truncatedUnderlyingComplex cm s₁ t)
      (truncatedUnderlyingComplex cm s₀ t) :=
  underlyingComplexMorphism
    (fun k' => cm.truncatedAMap s₁ k')
    (fun s k' => cm.truncatedFiltrationCompat s₁ s k')
    (fun k' => cm.truncatedAMap s₀ k')
    (fun s k' => cm.truncatedFiltrationCompat s₀ s k')
    (fun k' => F₁.truncationTransition h k')
    (fun k' => F₂.truncationTransition h k')
    (fun k' => truncatedAMap_naturality cm h k')
    (fun s k' => truncationTransition_fil_compat₁ h s k')
    (fun s k' => truncationTransition_fil_compat₂ h s k') t

/-- 截断复形转移在复形次数 `1` 的关联分次映射的显式形式。 -/
private theorem truncatedUCTransition_assocGradedMap_one
    (cm : ConvergenceMorphism conv₁ conv₂) {s₀ s₁ : ℤ} (h : s₀ ≤ s₁)
    (t : ω') (s : ℤ) :
    (truncatedUnderlyingComplexTransition cm h t).assocGradedMap s 1 =
      eqToHom (truncatedUC_assocGraded_one cm s₁ t s) ≫
        Filtration.inducedAssocGradedMap
          (fun k' => F₁.truncationTransition h k')
          (fun s' k' => truncationTransition_fil_compat₁ h s' k') s t ≫
        eqToHom (truncatedUC_assocGraded_one cm s₀ t s).symm := by
  simp only [FilteredComplexMorphism.assocGradedMap,
    truncatedUnderlyingComplexTransition, underlyingComplexMorphism,
    truncatedUnderlyingComplex, underlyingComplex, FilteredComplex.assocGraded,
    Filtration.associatedGraded, twoTermFil, twoTermObj, ↓reduceDIte,
    eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-- 截断复形转移在复形次数 `0` 的关联分次映射的显式形式。 -/
private theorem truncatedUCTransition_assocGradedMap_zero
    (cm : ConvergenceMorphism conv₁ conv₂) {s₀ s₁ : ℤ} (h : s₀ ≤ s₁)
    (t : ω') (s : ℤ) :
    (truncatedUnderlyingComplexTransition cm h t).assocGradedMap s 0 =
      eqToHom (truncatedUC_assocGraded_zero cm s₁ t s) ≫
        Filtration.inducedAssocGradedMap
          (fun k' => F₂.truncationTransition h k')
          (fun s' k' => truncationTransition_fil_compat₂ h s' k') s t ≫
        eqToHom (truncatedUC_assocGraded_zero cm s₀ t s).symm := by
  simp only [FilteredComplexMorphism.assocGradedMap,
    truncatedUnderlyingComplexTransition, underlyingComplexMorphism,
    truncatedUnderlyingComplex, underlyingComplex, FilteredComplex.assocGraded,
    Filtration.associatedGraded, twoTermFil, twoTermObj, ↓reduceDIte,
    eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-- 在有限窗口内，截断复形转移诱导的零页映射就是上述同构。 -/
private theorem truncatedUCTransition_assocGradedMap_eq_iso_hom
    (cm : ConvergenceMorphism conv₁ conv₂) {s₀ s₁ : ℤ} (h : s₀ ≤ s₁)
    (t : ω') (s k : ℤ) (hs : s ≤ s₀) :
    (truncatedUnderlyingComplexTransition cm h t).assocGradedMap s k =
      (truncatedUCAssocGradedTransitionIso cm h t s k hs).hom := by
  by_cases h₁ : k = 1
  · subst h₁
    rw [truncatedUCTransition_assocGradedMap_one cm h t s]
    simp [truncatedUCAssocGradedTransitionIso,
      truncatedAssociatedGradedTransitionIso₁_hom
        (F₁ := F₁) h s t hs]
  by_cases h₀ : k = 0
  · subst h₀
    rw [truncatedUCTransition_assocGradedMap_zero cm h t s]
    simp [truncatedUCAssocGradedTransitionIso,
      truncatedAssociatedGradedTransitionIso₂_hom
        (F₂ := F₂) h s t hs]
  · exact (truncatedUC_assocGraded_isZero_other
      cm s₁ t s k h₁ h₀).eq_of_src _ _

/-- 截断过滤复形态射诱导的谱序列态射。
    其页态射由底层态射规范诱导，微分交换性由过滤复形态射的函子性给出。 -/
noncomputable def truncatedESSTransition
    (cm : ConvergenceMorphism conv₁ conv₂)
    (hbb₁ : F₁.IsBoundedBelow) (hbb₂ : F₂.IsBoundedBelow)
    {s₀ s₁ : ℤ} (h : s₀ ≤ s₁) (t : ω') :
    SpectralSequenceMorphism (truncatedESS cm hbb₁ hbb₂ s₁ t)
      (truncatedESS cm hbb₁ hbb₂ s₀ t) := by
  let X : BoundedFilteredComplex C :=
    ⟨truncatedUnderlyingComplex cm s₁ t,
      truncatedUnderlyingComplex_isBounded cm hbb₁ hbb₂ s₁ t⟩
  let Y : BoundedFilteredComplex C :=
    ⟨truncatedUnderlyingComplex cm s₀ t,
      truncatedUnderlyingComplex_isBounded cm hbb₁ hbb₂ s₀ t⟩
  change SpectralSequenceMorphism
    (X.FC.toSpectralSequence X.bnd) (Y.FC.toSpectralSequence Y.bnd)
  exact FilteredComplexMorphism.toSpectralSequenceMorphism
    (truncatedUnderlyingComplexTransition cm h t : X ⟶ Y)

/-! ### Section 3: Stabilization -/

/-! ### Section 4: Unbounded extension spectral sequence -/

variable [LocallySmall.{w₀} C] [WellPowered.{w₀} C]
variable [HasWidePullbacks.{w₀} C] [HasCoproducts.{w₀} C]

/-- 由原始 `E∞` 环境中的有限循环、边缘和微分数据组装出的无界扩张谱序列。
有界下条件保留在公开接口中，供后续与截断稳定性及收敛定理衔接；核心构造本身不依赖它。 -/
noncomputable def UnboundedExtensionSS
    (cm : ConvergenceMorphism conv₁ conv₂)
    (hbb₁ : F₁.IsBoundedBelow) (hbb₂ : F₂.IsBoundedBelow) (t : ω') :
    SpectralSequence C (ℤ × ℤ) :=
  unboundedExtensionSpectralSequenceCore cm t

/-- 公开的 `UnboundedExtensionSS` 与不带冗余假设的核心构造定义相等。 -/
@[simp]
theorem UnboundedExtensionSS_eq_ExtensionSpectralSequence
    (cm : ConvergenceMorphism conv₁ conv₂)
    (hbb₁ : F₁.IsBoundedBelow) (hbb₂ : F₂.IsBoundedBelow) (t : ω') :
    UnboundedExtensionSS cm hbb₁ hbb₂ t = ExtensionSpectralSequence cm t :=
  rfl

/-- 公开的无界扩张谱序列使用的正是原始 `E∞` 环境中的 `SSData`。 -/
@[simp]
theorem UnboundedExtensionSS_ssData
    (cm : ConvergenceMorphism conv₁ conv₂)
    (hbb₁ : F₁.IsBoundedBelow) (hbb₂ : F₂.IsBoundedBelow)
    (t : ω') (sk : ℤ × ℤ) :
    (UnboundedExtensionSS cm hbb₁ hbb₂ t).ssData sk =
      unboundedExtensionSSData cm t sk := rfl

/-- 公开的无界扩张谱序列在自然数页上的微分就是独立构造的无界微分。 -/
theorem UnboundedExtensionSS_d_nat
    (cm : ConvergenceMorphism conv₁ conv₂)
    (hbb₁ : F₁.IsBoundedBelow) (hbb₂ : F₂.IsBoundedBelow)
    (t : ω') (s k : ℤ) (n : ℕ) :
    (UnboundedExtensionSS cm hbb₁ hbb₂ t).d (n : ℤ) (s, k) =
      unboundedExtensionDifferential cm t s k n := by
  change (unboundedExtensionPreSS cm t).d (n : ℤ) (s, k) = _
  exact unboundedExtensionPreSS_d_nat cm t s k n

/-- 公开无界扩张谱序列的有限页与未截断两项复形有限页的规范同构。 -/
noncomputable def UnboundedExtensionSS.finitePageIso
    (cm : ConvergenceMorphism conv₁ conv₂)
    (hbb₁ : F₁.IsBoundedBelow) (hbb₂ : F₂.IsBoundedBelow)
    (t : ω') (s k : ℤ) (n : ℕ) :
    (UnboundedExtensionSS cm hbb₁ hbb₂ t).Page (n : ℤ) (s, k) ≅
      (unboundedUnderlyingComplex cm t).finitePage s k n := by
  change ((unboundedExtensionSSData cm t) (s, k)).page (n : WithTop ℕ) ≅ _
  exact unboundedExtensionPageIso cm t (s, k) n ≪≫
    eqToIso (unboundedComplexSSData_page_nat cm t s k n)

/-- 对任意整数页，公开无界扩张页由对应的自然数有限页给出。
负页按谱序列的约定统一取第零个有限页。 -/
noncomputable def UnboundedExtensionSS.pageComplexIso
    (cm : ConvergenceMorphism conv₁ conv₂)
    (hbb₁ : F₁.IsBoundedBelow) (hbb₂ : F₂.IsBoundedBelow)
    (t : ω') (s k r : ℤ) :
    (UnboundedExtensionSS cm hbb₁ hbb₂ t).Page r (s, k) ≅
      (unboundedUnderlyingComplex cm t).finitePage s k r.toNat := by
  change ((unboundedExtensionSSData cm t) (s, k)).page
      ((r - 0).toNat : WithTop ℕ) ≅ _
  simpa only [sub_zero] using
    (unboundedExtensionPageIso cm t (s, k) r.toNat ≪≫
      eqToIso (unboundedComplexSSData_page_nat cm t s k r.toNat))

/-- 截断扩张谱序列的自然数页就是相应截断两项复形的有限页。 -/
private noncomputable def truncatedESSFinitePageIso
    (cm : ConvergenceMorphism conv₁ conv₂)
    (hbb₁ : F₁.IsBoundedBelow) (hbb₂ : F₂.IsBoundedBelow)
    (s₀ : ℤ) (t : ω') (s k : ℤ) (n : ℕ) :
    (truncatedESS cm hbb₁ hbb₂ s₀ t).Page (n : ℤ) (s, k) ≅
      (truncatedUnderlyingComplex cm s₀ t).finitePage s k n := by
  change (((truncatedUnderlyingComplex cm s₀ t).toSSData
      (truncatedUnderlyingComplex_isBounded cm hbb₁ hbb₂ s₀ t) s k).page
        (n : WithTop ℕ)) ≅ _
  exact FilteredComplex.finitePageIso
    (truncatedUnderlyingComplex cm s₀ t)
    (truncatedUnderlyingComplex_isBounded cm hbb₁ hbb₂ s₀ t) s k n

/-- 截断扩张谱序列的任意整数页由对应的自然数有限页给出。 -/
private noncomputable def truncatedESSPageComplexIso
    (cm : ConvergenceMorphism conv₁ conv₂)
    (hbb₁ : F₁.IsBoundedBelow) (hbb₂ : F₂.IsBoundedBelow)
    (s₀ : ℤ) (t : ω') (s k r : ℤ) :
    (truncatedESS cm hbb₁ hbb₂ s₀ t).Page r (s, k) ≅
      (truncatedUnderlyingComplex cm s₀ t).finitePage s k r.toNat := by
  change (((truncatedUnderlyingComplex cm s₀ t).toSSData
      (truncatedUnderlyingComplex_isBounded cm hbb₁ hbb₂ s₀ t) s k).page
        ((r - 0).toNat : WithTop ℕ)) ≅ _
  simpa only [sub_zero] using
    FilteredComplex.finitePageIso
      (truncatedUnderlyingComplex cm s₀ t)
      (truncatedUnderlyingComplex_isBounded cm hbb₁ hbb₂ s₀ t)
      s k r.toNat

/-- 在覆盖循环条件所需有限窗口后，次数 `1` 的未截断有限页
与截断有限页同构。 -/
private noncomputable def unboundedFinitePageTruncatedIsoOne
    (cm : ConvergenceMorphism conv₁ conv₂) (s₀ : ℤ) (t : ω')
    (s : ℤ) (n : ℕ) (hs : s ≤ s₀) (hcycle : s + ↑n ≤ s₀ + 1) :
    (unboundedUnderlyingComplex cm t).finitePage s 1 n ≅
      (truncatedUnderlyingComplex cm s₀ t).finitePage s 1 n := by
  let e := unboundedUCAssocGradedProjectionIso cm s₀ t s 1 hs
  apply filteredComplexFinitePageIsoOfSubobjectEq
    (unboundedUnderlyingComplex cm t)
    (truncatedUnderlyingComplex cm s₀ t) s 1 n e
  · rw [unboundedUC_boundarySubobject_one_eq_bot,
      truncatedUC_boundarySubobject_one_eq_bot]
    exact (Subobject.mapIsoToOrderIso e).map_bot
  · exact unboundedUCProjection_map_cycleSubobject_one_eq
      cm s₀ t s n hs hcycle

/-- 在覆盖当前关联分次后，次数 `0` 的未截断有限页
与截断有限页同构。 -/
private noncomputable def unboundedFinitePageTruncatedIsoZero
    (cm : ConvergenceMorphism conv₁ conv₂) (s₀ : ℤ) (t : ω')
    (s : ℤ) (n : ℕ) (hs : s ≤ s₀) :
    (unboundedUnderlyingComplex cm t).finitePage s 0 n ≅
      (truncatedUnderlyingComplex cm s₀ t).finitePage s 0 n := by
  let e := unboundedUCAssocGradedProjectionIso cm s₀ t s 0 hs
  apply filteredComplexFinitePageIsoOfSubobjectEq
    (unboundedUnderlyingComplex cm t)
    (truncatedUnderlyingComplex cm s₀ t) s 0 n e
  · exact unboundedUCProjection_map_boundarySubobject_zero_eq
      cm s₀ t s n hs
  · rw [unboundedUC_cycleSubobject_zero_eq_top,
      truncatedUC_cycleSubobject_zero_eq_top]
    exact (Subobject.mapIsoToOrderIso e).map_top

/-- 截断层覆盖当前过滤次数时，无界扩张与截断扩张的第零页同构。 -/
private noncomputable def UnboundedExtensionSS.pageZeroIso
    (cm : ConvergenceMorphism conv₁ conv₂)
    (hbb₁ : F₁.IsBoundedBelow) (hbb₂ : F₂.IsBoundedBelow)
    (s₀ : ℤ) (t : ω') (s k : ℤ) (hs : s ≤ s₀) :
    (UnboundedExtensionSS cm hbb₁ hbb₂ t).Page 0 (s, k) ≅
      (truncatedESS cm hbb₁ hbb₂ s₀ t).Page 0 (s, k) :=
  UnboundedExtensionSS.finitePageIso cm hbb₁ hbb₂ t s k 0 ≪≫
    unboundedFinitePageZeroTruncatedIso cm s₀ t s k hs ≪≫
    (truncatedESSFinitePageIso cm hbb₁ hbb₂ s₀ t s k 0).symm

/-- 非正整数页按约定都取第零有限页，因此同一个零页窗口同构同时处理它们。 -/
private noncomputable def UnboundedExtensionSS.pageIsoOfNonpos
    (cm : ConvergenceMorphism conv₁ conv₂)
    (hbb₁ : F₁.IsBoundedBelow) (hbb₂ : F₂.IsBoundedBelow)
    (s₀ : ℤ) (t : ω') (s k r : ℤ) (hr : r ≤ 0) (hs : s ≤ s₀) :
    (UnboundedExtensionSS cm hbb₁ hbb₂ t).Page r (s, k) ≅
      (truncatedESS cm hbb₁ hbb₂ s₀ t).Page r (s, k) := by
  have hrnat : r.toNat = 0 := Int.toNat_eq_zero.mpr hr
  change ((unboundedExtensionSSData cm t) (s, k)).page
      ((r - 0).toNat : WithTop ℕ) ≅
    (((truncatedUnderlyingComplex cm s₀ t).toSSData
      (truncatedUnderlyingComplex_isBounded cm hbb₁ hbb₂ s₀ t) s k).page
        ((r - 0).toNat : WithTop ℕ))
  simp only [sub_zero, hrnat]
  exact UnboundedExtensionSS.pageZeroIso cm hbb₁ hbb₂ s₀ t s k hs

/-- 两项复形次数之外两边的所有页均为零，因而无需任何截断深度条件。 -/
private noncomputable def UnboundedExtensionSS.pageIsoOfOtherDegree
    (cm : ConvergenceMorphism conv₁ conv₂)
    (hbb₁ : F₁.IsBoundedBelow) (hbb₂ : F₂.IsBoundedBelow)
    (s₀ : ℤ) (t : ω') (s k r : ℤ) (h₁ : k ≠ 1) (h₀ : k ≠ 0) :
    (UnboundedExtensionSS cm hbb₁ hbb₂ t).Page r (s, k) ≅
      (truncatedESS cm hbb₁ hbb₂ s₀ t).Page r (s, k) := by
  let hU : IsZero
      ((unboundedUnderlyingComplex cm t).finitePage s k r.toNat) :=
    filteredComplexFinitePageIsZero (unboundedUnderlyingComplex cm t)
      s k r.toNat (unboundedUC_assocGraded_isZero_other cm t s k h₁ h₀)
  let hT : IsZero
      ((truncatedUnderlyingComplex cm s₀ t).finitePage s k r.toNat) :=
    filteredComplexFinitePageIsZero (truncatedUnderlyingComplex cm s₀ t)
      s k r.toNat
      (truncatedUC_assocGraded_isZero_other cm s₀ t s k h₁ h₀)
  exact UnboundedExtensionSS.pageComplexIso cm hbb₁ hbb₂ t s k r ≪≫
    IsZero.iso hU hT ≪≫
    (by
      change (truncatedUnderlyingComplex cm s₀ t).finitePage s k r.toNat ≅
        (((truncatedUnderlyingComplex cm s₀ t).toSSData
          (truncatedUnderlyingComplex_isBounded cm hbb₁ hbb₂ s₀ t) s k).page
            ((r - 0).toNat : WithTop ℕ))
      simpa only [sub_zero] using
        (FilteredComplex.finitePageIso
          (truncatedUnderlyingComplex cm s₀ t)
          (truncatedUnderlyingComplex_isBounded cm hbb₁ hbb₂ s₀ t)
          s k r.toNat).symm)

/-- 无界扩张的每个固定页是充分深截断页的稳定值。 -/
theorem UnboundedExtensionSS.pageIso
    (cm : ConvergenceMorphism conv₁ conv₂)
    (hbb₁ : F₁.IsBoundedBelow) (hbb₂ : F₂.IsBoundedBelow)
    (t : ω') (sk : ℤ × ℤ) (r : ℤ) :
    ∃ s₀_min : ℤ, ∀ s₀ ≥ s₀_min,
      Nonempty ((UnboundedExtensionSS cm hbb₁ hbb₂ t).Page r sk ≅
        (truncatedESS cm hbb₁ hbb₂ s₀ t).Page r sk) := by
  rcases sk with ⟨s, k⟩
  by_cases hr : r ≤ 0
  · refine ⟨s, fun s₀ hs₀ => ?_⟩
    exact ⟨UnboundedExtensionSS.pageIsoOfNonpos
      cm hbb₁ hbb₂ s₀ t s k r hr hs₀⟩
  · let n := r.toNat
    refine ⟨s + (n : ℤ), fun s₀ hs₀ => ?_⟩
    have hs : s ≤ s₀ := by omega
    have hcycle : s + (n : ℤ) ≤ s₀ + 1 := by omega
    by_cases hk₁ : k = 1
    · subst hk₁
      exact ⟨UnboundedExtensionSS.pageComplexIso
          cm hbb₁ hbb₂ t s 1 r ≪≫
        unboundedFinitePageTruncatedIsoOne cm s₀ t s n hs hcycle ≪≫
        (truncatedESSPageComplexIso
          cm hbb₁ hbb₂ s₀ t s 1 r).symm⟩
    by_cases hk₀ : k = 0
    · subst hk₀
      exact ⟨UnboundedExtensionSS.pageComplexIso
          cm hbb₁ hbb₂ t s 0 r ≪≫
        unboundedFinitePageTruncatedIsoZero cm s₀ t s n hs ≪≫
        (truncatedESSPageComplexIso
          cm hbb₁ hbb₂ s₀ t s 0 r).symm⟩
    · exact ⟨UnboundedExtensionSS.pageIsoOfOtherDegree
        cm hbb₁ hbb₂ s₀ t s k r hk₁ hk₀⟩

/-- 对每个固定页和双次数，截断越过有限过滤窗口后页对象稳定。
两个充分深的截断页都与同一个无界页同构，因而彼此同构。 -/
theorem truncatedESS_pageStabilization
    (cm : ConvergenceMorphism conv₁ conv₂)
    (hbb₁ : F₁.IsBoundedBelow) (hbb₂ : F₂.IsBoundedBelow)
    (t : ω') (sk : ℤ × ℤ) (r : ℤ) :
    ∃ s₀_min : ℤ, ∀ s₀ ≥ s₀_min,
      Nonempty ((truncatedESS cm hbb₁ hbb₂ s₀ t).Page r sk ≅
        (truncatedESS cm hbb₁ hbb₂ s₀_min t).Page r sk) := by
  obtain ⟨s₀_min, hstable⟩ :=
    UnboundedExtensionSS.pageIso cm hbb₁ hbb₂ t sk r
  refine ⟨s₀_min, fun s₀ hs₀ => ?_⟩
  exact ⟨(hstable s₀ hs₀).some.symm ≪≫
    (hstable s₀_min le_rfl).some⟩

/-! ### Section 5: Convergence -/

/-- 两个子对象嵌入同一子对象后所得的像相等，则原子对象相等。 -/
private theorem subobject_eq_of_image_ofLE_eq
    {X : C} {P Q R : Subobject X} (hP : P ≤ R) (hQ : Q ≤ R)
    (h : imageSubobject (Subobject.ofLE P R hP) =
      imageSubobject (Subobject.ofLE Q R hQ)) : P = Q := by
  have hmk : Subobject.mk (Subobject.ofLE P R hP) =
      Subobject.mk (Subobject.ofLE Q R hQ) := by
    simpa only [imageSubobject_mono] using h
  have hPmap : (Subobject.map R.arrow).obj
      (Subobject.mk (Subobject.ofLE P R hP)) = P := by
    rw [Subobject.map_mk]
    exact Subobject.mk_eq_of_comm _ (Iso.refl _)
      (by simp only [Iso.refl_hom, Category.id_comp, Subobject.ofLE_arrow])
  have hQmap : (Subobject.map R.arrow).obj
      (Subobject.mk (Subobject.ofLE Q R hQ)) = Q := by
    rw [Subobject.map_mk]
    exact Subobject.mk_eq_of_comm _ (Iso.refl _)
      (by simp only [Iso.refl_hom, Category.id_comp, Subobject.ofLE_arrow])
  rw [← hPmap, ← hQmap, hmk]

/-- 有界下且满足 Mittag--Leffler 条件的递减过滤在每个次数上最终常值。 -/
private theorem Filtration.eventually_constant_of_mittagLeffler
    {A : ω' → C} (F : Filtration A) (hbb : F.IsBoundedBelow)
    (hml : F.IsMittagLeffler) (t : ω') :
    ∃ s₀ : ℤ, ∀ s ≥ s₀, F.F s t = F.F s₀ t := by
  obtain ⟨N, hN⟩ := hml t (hbb.lo t)
  refine ⟨hbb.lo t + (N : ℤ), fun s hs => ?_⟩
  let n : ℕ := (s - hbb.lo t).toNat
  have hn : N ≤ n := by
    dsimp only [n]
    omega
  have hs_eq : hbb.lo t + (n : ℤ) = s := by
    dsimp only [n]
    omega
  have himage := hN n hn
  rw [← hs_eq]
  apply subobject_eq_of_image_ofLE_eq
    (F.mono_of_le (show hbb.lo t ≤ hbb.lo t + (n : ℤ) by omega) t)
    (F.mono_of_le (show hbb.lo t ≤ hbb.lo t + (N : ℤ) by omega) t)
  exact himage

/-- 若循环塔和边缘塔从某一有限页起常值，则顶页就是该有限页。 -/
private noncomputable def SSData.eInftyIsoPageOfStable
    (D : SSData C) (n : ℕ)
    (hZ : ∀ m ≥ n, D.Z (m : WithTop ℕ) = D.Z (n : WithTop ℕ))
    (hB : ∀ m ≥ n, D.B (m : WithTop ℕ) = D.B (n : WithTop ℕ)) :
    D.eInfty ≅ D.page (n : WithTop ℕ) := by
  have hZtop : D.Z ⊤ = D.Z (n : WithTop ℕ) := by
    apply le_antisymm (D.Z_anti le_top)
    apply D.Z_top_greatest
    intro m
    by_cases hm : n ≤ m
    · rw [hZ m hm]
    · exact D.Z_anti (by exact_mod_cast Nat.le_of_not_ge hm)
  have hBtop : D.B ⊤ = D.B (n : WithTop ℕ) := by
    apply le_antisymm
    · apply D.B_top_least
      intro m
      by_cases hm : n ≤ m
      · rw [hB m hm]
      · exact D.B_mono (by exact_mod_cast Nat.le_of_not_ge hm)
    · exact D.B_mono le_top
  let BT := D.B ⊤
  let BN := D.B (n : WithTop ℕ)
  let ZT := D.Z ⊤
  let ZN := D.Z (n : WithTop ℕ)
  let eB : (BT : C) ≅ (BN : C) :=
    eqToIso (congrArg Subobject.underlying.obj hBtop)
  let eZ : (ZT : C) ≅ (ZN : C) :=
    eqToIso (congrArg Subobject.underlying.obj hZtop)
  let iT := Subobject.ofLE BT ZT (D.B_le_Z ⊤)
  let iN := Subobject.ofLE BN ZN (D.B_le_Z (n : WithTop ℕ))
  have heB : eB.hom ≫ BN.arrow = BT.arrow := by
    exact Subobject.arrow_congr BT BN hBtop
  have heZ : eZ.hom ≫ ZN.arrow = ZT.arrow := by
    exact Subobject.arrow_congr ZT ZN hZtop
  have hsquare : iT ≫ eZ.hom = eB.hom ≫ iN := by
    apply (cancel_mono ZN.arrow).1
    calc
      (iT ≫ eZ.hom) ≫ ZN.arrow = iT ≫ (eZ.hom ≫ ZN.arrow) :=
        Category.assoc _ _ _
      _ = iT ≫ ZT.arrow := by rw [heZ]
      _ = BT.arrow := Subobject.ofLE_arrow _
      _ = eB.hom ≫ BN.arrow := heB.symm
      _ = (eB.hom ≫ iN) ≫ ZN.arrow := by
        rw [Category.assoc, Subobject.ofLE_arrow]
  change cokernel iT ≅ cokernel iN
  exact cokernel.mapIso iT iN eB eZ hsquare

/-- 过滤在循环条件所见的目标层上相等时，相应有限循环子对象相等。 -/
private theorem FilteredComplex.cycleSubobject_nat_eq_of_fil_eq
    (FC : FilteredComplex C) (s k : ℤ) (m n : ℕ)
    (h : FC.fil (s + (m : ℤ)) (k - 1) =
      FC.fil (s + (n : ℤ)) (k - 1)) :
    FC.cycleSubobject s k (m : WithTop ℕ) =
      FC.cycleSubobject s k (n : WithTop ℕ) := by
  simp only [FilteredComplex.cycleSubobject]
  change imageSubobject
      ((kernelSubobject ((FC.fil s k).arrow ≫ FC.d k ≫
        cokernel.π ((FC.fil (s + (m : ℤ)) (k - 1)).arrow))).arrow ≫
        FC.filToAssocGraded s k) =
    imageSubobject
      ((kernelSubobject ((FC.fil s k).arrow ≫ FC.d k ≫
        cokernel.π ((FC.fil (s + (n : ℤ)) (k - 1)).arrow))).arrow ≫
        FC.filToAssocGraded s k)
  rw [h]

/-- 过滤在边缘来源层上相等时，相应有限边缘子对象相等。 -/
private theorem FilteredComplex.boundarySubobject_nat_eq_of_fil_eq
    (FC : FilteredComplex C) (s k : ℤ) (m n : ℕ)
    (h : FC.fil (s - (m : ℤ) + 1) (k + 1) =
      FC.fil (s - (n : ℤ) + 1) (k + 1)) :
    FC.boundarySubobject s k (m : WithTop ℕ) =
      FC.boundarySubobject s k (n : WithTop ℕ) := by
  simp only [FilteredComplex.boundarySubobject]
  change imageSubobject
      (Subobject.ofLE
        (imageSubobject
          ((FC.fil (s - (m : ℤ) + 1) (k + 1)).arrow ≫ FC.dToK k) ⊓
            FC.fil s k)
        (FC.fil s k) inf_le_right ≫ FC.filToAssocGraded s k) =
    imageSubobject
      (Subobject.ofLE
        (imageSubobject
          ((FC.fil (s - (n : ℤ) + 1) (k + 1)).arrow ≫ FC.dToK k) ⊓
            FC.fil s k)
        (FC.fil s k) inf_le_right ≫ FC.filToAssocGraded s k)
  rw [h]

/-- 次数 `1` 中，深层过滤最终常值时，无界复形数据的顶页由一个有限页实现。 -/
private noncomputable def unboundedComplexEInftyIsoFiniteOne
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω') (s₀ s : ℤ)
    (hstable₂ : ∀ q ≥ s₀, F₂.F q t = F₂.F s₀ t) (hs : s ≤ s₀) :
    (unboundedComplexSSData cm t s 1).eInfty ≅
      (unboundedUnderlyingComplex cm t).finitePage s 1
        (s₀ + 1 - s).toNat := by
  let n := (s₀ + 1 - s).toNat
  have hn : s + (n : ℤ) = s₀ + 1 := by
    dsimp only [n]
    omega
  refine SSData.eInftyIsoPageOfStable
      (unboundedComplexSSData cm t s 1) n ?_ ?_ ≪≫
    eqToIso (unboundedComplexSSData_page_nat cm t s 1 n)
  · intro m hm
    change (unboundedUnderlyingComplex cm t).cycleSubobject s 1
        (m : WithTop ℕ) =
      (unboundedUnderlyingComplex cm t).cycleSubobject s 1
        (n : WithTop ℕ)
    apply FilteredComplex.cycleSubobject_nat_eq_of_fil_eq
    change F₂.F (s + (m : ℤ)) t = F₂.F (s + (n : ℤ)) t
    rw [hstable₂ (s + (m : ℤ)) (by omega),
      hstable₂ (s + (n : ℤ)) (by omega)]
  · intro m hm
    change (unboundedUnderlyingComplex cm t).boundarySubobject s 1
        (m : WithTop ℕ) =
      (unboundedUnderlyingComplex cm t).boundarySubobject s 1
        (n : WithTop ℕ)
    rw [unboundedUC_boundarySubobject_one_eq_bot,
      unboundedUC_boundarySubobject_one_eq_bot]

/-- 次数 `1` 中，截断复形数据的顶页由截断层对应的有限页实现。 -/
private noncomputable def truncatedComplexEInftyIsoFiniteOne
    (cm : ConvergenceMorphism conv₁ conv₂)
    (hbb₁ : F₁.IsBoundedBelow) (hbb₂ : F₂.IsBoundedBelow)
    (s₀ : ℤ) (t : ω') (s : ℤ) (hs : s ≤ s₀) :
    ((truncatedUnderlyingComplex cm s₀ t).toSSData
      (truncatedUnderlyingComplex_isBounded cm hbb₁ hbb₂ s₀ t) s 1).eInfty ≅
      (truncatedUnderlyingComplex cm s₀ t).finitePage s 1
        (s₀ + 1 - s).toNat := by
  let FC := truncatedUnderlyingComplex cm s₀ t
  let bnd := truncatedUnderlyingComplex_isBounded cm hbb₁ hbb₂ s₀ t
  let n := (s₀ + 1 - s).toNat
  have hn : s + (n : ℤ) = s₀ + 1 := by
    dsimp only [n]
    omega
  refine SSData.eInftyIsoPageOfStable (FC.toSSData bnd s 1) n ?_ ?_ ≪≫
    FilteredComplex.finitePageIso FC bnd s 1 n
  · intro m hm
    change FC.cycleSubobject s 1 (m : WithTop ℕ) =
      FC.cycleSubobject s 1 (n : WithTop ℕ)
    apply FilteredComplex.cycleSubobject_nat_eq_of_fil_eq
    change (F₂.truncatedFiltration s₀).F (s + (m : ℤ)) t =
      (F₂.truncatedFiltration s₀).F (s + (n : ℤ)) t
    rw [(F₂.truncatedFiltration_isBounded hbb₂ s₀).boundedAbove t
        (s + (m : ℤ)) (by change s₀ + 1 ≤ s + (m : ℤ); omega),
      (F₂.truncatedFiltration_isBounded hbb₂ s₀).boundedAbove t
        (s + (n : ℤ)) (by change s₀ + 1 ≤ s + (n : ℤ); omega)]
  · intro m hm
    change FC.boundarySubobject s 1 (m : WithTop ℕ) =
      FC.boundarySubobject s 1 (n : WithTop ℕ)
    dsimp only [FC]
    rw [truncatedUC_boundarySubobject_one_eq_bot,
      truncatedUC_boundarySubobject_one_eq_bot]

/-- 次数 `0` 中，有界下条件使无界复形数据的顶页由一个有限页实现。 -/
private noncomputable def unboundedComplexEInftyIsoFiniteZero
    (cm : ConvergenceMorphism conv₁ conv₂)
    (hbb₁ : F₁.IsBoundedBelow) (s₀ : ℤ) (t : ω') (s : ℤ) :
    (unboundedComplexSSData cm t s 0).eInfty ≅
      (unboundedUnderlyingComplex cm t).finitePage s 0
        (s + 1 - min (hbb₁.lo t) (s₀ + 1)).toNat := by
  let q₀ := min (hbb₁.lo t) (s₀ + 1)
  let n := (s + 1 - q₀).toNat
  have hq : s - (n : ℤ) + 1 ≤ q₀ := by
    dsimp only [n, q₀]
    omega
  refine SSData.eInftyIsoPageOfStable
      (unboundedComplexSSData cm t s 0) n ?_ ?_ ≪≫
    eqToIso (unboundedComplexSSData_page_nat cm t s 0 n)
  · intro m hm
    change (unboundedUnderlyingComplex cm t).cycleSubobject s 0
        (m : WithTop ℕ) =
      (unboundedUnderlyingComplex cm t).cycleSubobject s 0
        (n : WithTop ℕ)
    rw [unboundedUC_cycleSubobject_zero_eq_top,
      unboundedUC_cycleSubobject_zero_eq_top]
  · intro m hm
    have hqm : s - (m : ℤ) + 1 ≤ q₀ := le_trans (by omega) hq
    change (unboundedUnderlyingComplex cm t).boundarySubobject s 0
        (m : WithTop ℕ) =
      (unboundedUnderlyingComplex cm t).boundarySubobject s 0
        (n : WithTop ℕ)
    apply FilteredComplex.boundarySubobject_nat_eq_of_fil_eq
    change F₁.F (s - (m : ℤ) + 1) t = F₁.F (s - (n : ℤ) + 1) t
    rw [hbb₁.boundedBelow t (s - (m : ℤ) + 1)
        (le_trans hqm (min_le_left _ _)),
      hbb₁.boundedBelow t (s - (n : ℤ) + 1)
        (by exact le_trans hq (min_le_left _ _))]

/-- 次数 `0` 中，截断复形数据的顶页由同一个有界下有限页实现。 -/
private noncomputable def truncatedComplexEInftyIsoFiniteZero
    (cm : ConvergenceMorphism conv₁ conv₂)
    (hbb₁ : F₁.IsBoundedBelow) (hbb₂ : F₂.IsBoundedBelow)
    (s₀ : ℤ) (t : ω') (s : ℤ) :
    ((truncatedUnderlyingComplex cm s₀ t).toSSData
      (truncatedUnderlyingComplex_isBounded cm hbb₁ hbb₂ s₀ t) s 0).eInfty ≅
      (truncatedUnderlyingComplex cm s₀ t).finitePage s 0
        (s + 1 - min (hbb₁.lo t) (s₀ + 1)).toNat := by
  let FC := truncatedUnderlyingComplex cm s₀ t
  let bnd := truncatedUnderlyingComplex_isBounded cm hbb₁ hbb₂ s₀ t
  let q₀ := min (hbb₁.lo t) (s₀ + 1)
  let n := (s + 1 - q₀).toNat
  have hq : s - (n : ℤ) + 1 ≤ q₀ := by
    dsimp only [n, q₀]
    omega
  refine SSData.eInftyIsoPageOfStable (FC.toSSData bnd s 0) n ?_ ?_ ≪≫
    FilteredComplex.finitePageIso FC bnd s 0 n
  · intro m hm
    change FC.cycleSubobject s 0 (m : WithTop ℕ) =
      FC.cycleSubobject s 0 (n : WithTop ℕ)
    dsimp only [FC]
    rw [truncatedUC_cycleSubobject_zero_eq_top,
      truncatedUC_cycleSubobject_zero_eq_top]
  · intro m hm
    change FC.boundarySubobject s 0 (m : WithTop ℕ) =
      FC.boundarySubobject s 0 (n : WithTop ℕ)
    apply FilteredComplex.boundarySubobject_nat_eq_of_fil_eq
    change (F₁.truncatedFiltration s₀).F (s - (m : ℤ) + 1) t =
      (F₁.truncatedFiltration s₀).F (s - (n : ℤ) + 1) t
    rw [(F₁.truncatedFiltration_isBounded hbb₁ s₀).boundedBelow t
        (s - (m : ℤ) + 1)
        (by change s - (m : ℤ) + 1 ≤ min (hbb₁.lo t) (s₀ + 1); omega),
      (F₁.truncatedFiltration_isBounded hbb₁ s₀).boundedBelow t
        (s - (n : ℤ) + 1)
        (by change s - (n : ℤ) + 1 ≤ min (hbb₁.lo t) (s₀ + 1); exact hq)]

/-- 关联分次相邻两层相等时，该关联分次对象为零。 -/
private theorem Filtration.associatedGraded_isZero_of_eq
    {A : ω' → C} (F : Filtration A) (s : ℤ) (t : ω')
    (h : F.F (s + 1) t = F.F s t) :
    IsZero (F.associatedGraded s t) := by
  unfold Filtration.associatedGraded
  haveI : IsIso (Subobject.ofLE (F.F (s + 1) t) (F.F s t) (F.mono s t)) := by
    rw [← Subobject.isoOfEq_hom _ _ h]
    infer_instance
  exact isZero_cokernel_of_epi _

/-- `SSData` 的环境对象为零时，其顶页也为零。 -/
private theorem SSData.eInfty_isZero_of_V (D : SSData C) (hV : IsZero D.V) :
    IsZero D.eInfty := by
  have hZ : IsZero (Subobject.underlying.obj (D.Z ⊤)) :=
    hV.of_mono (D.Z ⊤).arrow
  haveI : Epi (D.pageπ ⊤) := by
    unfold SSData.pageπ
    infer_instance
  exact hZ.of_epi (D.pageπ ⊤)

/-- 在最终常值截断处，无界扩张与相应截断扩张的顶页逐双次数同构。 -/
private noncomputable def UnboundedExtensionSS.eInftyIsoTruncated
    (cm : ConvergenceMorphism conv₁ conv₂)
    (hbb₁ : F₁.IsBoundedBelow) (hbb₂ : F₂.IsBoundedBelow)
    (s₀ : ℤ) (t : ω')
    (hstable₁ : ∀ q ≥ s₀, F₁.F q t = F₁.F s₀ t)
    (hstable₂ : ∀ q ≥ s₀, F₂.F q t = F₂.F s₀ t)
    (s k : ℤ) :
    ((UnboundedExtensionSS cm hbb₁ hbb₂ t).ssData (s, k)).eInfty ≅
      ((truncatedESS cm hbb₁ hbb₂ s₀ t).ssData (s, k)).eInfty := by
  change (unboundedExtensionSSData cm t (s, k)).eInfty ≅
    ((truncatedUnderlyingComplex cm s₀ t).toSSData
      (truncatedUnderlyingComplex_isBounded cm hbb₁ hbb₂ s₀ t) s k).eInfty
  by_cases hk₁ : k = 1
  · subst hk₁
    by_cases hs : s ≤ s₀
    · let n := (s₀ + 1 - s).toNat
      exact unboundedExtensionPageIsoWithTop cm t (s, 1) ⊤ ≪≫
        unboundedComplexEInftyIsoFiniteOne cm t s₀ s hstable₂ hs ≪≫
        unboundedFinitePageTruncatedIsoOne cm s₀ t s n hs (by
          dsimp only [n]
          omega) ≪≫
        (truncatedComplexEInftyIsoFiniteOne
          cm hbb₁ hbb₂ s₀ t s hs).symm
    · have hs' : s₀ ≤ s := le_of_lt (lt_of_not_ge hs)
      have hgrU : IsZero
          ((unboundedUnderlyingComplex cm t).assocGraded s 1) := by
        rw [unboundedUC_assocGraded_one]
        apply Filtration.associatedGraded_isZero_of_eq
        rw [hstable₁ (s + 1) (by omega), hstable₁ s hs']
      have hgrT : IsZero
          ((truncatedUnderlyingComplex cm s₀ t).assocGraded s 1) := by
        rw [truncatedUC_assocGraded_one]
        apply Filtration.associatedGraded_isZero_of_eq
        rw [(F₁.truncatedFiltration_isBounded hbb₁ s₀).boundedAbove t
              (s + 1) (by change s₀ + 1 ≤ s + 1; omega),
          (F₁.truncatedFiltration_isBounded hbb₁ s₀).boundedAbove t
              s (by change s₀ + 1 ≤ s; omega)]
      exact unboundedExtensionPageIsoWithTop cm t (s, 1) ⊤ ≪≫
        IsZero.iso
          (SSData.eInfty_isZero_of_V
            (unboundedComplexSSData cm t s 1) hgrU)
          (SSData.eInfty_isZero_of_V
            ((truncatedUnderlyingComplex cm s₀ t).toSSData
              (truncatedUnderlyingComplex_isBounded cm hbb₁ hbb₂ s₀ t) s 1) hgrT)
  · by_cases hk₀ : k = 0
    · subst hk₀
      by_cases hs : s ≤ s₀
      · let n := (s + 1 - min (hbb₁.lo t) (s₀ + 1)).toNat
        exact unboundedExtensionPageIsoWithTop cm t (s, 0) ⊤ ≪≫
          unboundedComplexEInftyIsoFiniteZero cm hbb₁ s₀ t s ≪≫
          unboundedFinitePageTruncatedIsoZero cm s₀ t s n hs ≪≫
          (truncatedComplexEInftyIsoFiniteZero
            cm hbb₁ hbb₂ s₀ t s).symm
      · have hs' : s₀ ≤ s := le_of_lt (lt_of_not_ge hs)
        have hgrU : IsZero
            ((unboundedUnderlyingComplex cm t).assocGraded s 0) := by
          rw [unboundedUC_assocGraded_zero]
          apply Filtration.associatedGraded_isZero_of_eq
          rw [hstable₂ (s + 1) (by omega), hstable₂ s hs']
        have hgrT : IsZero
            ((truncatedUnderlyingComplex cm s₀ t).assocGraded s 0) := by
          rw [truncatedUC_assocGraded_zero]
          apply Filtration.associatedGraded_isZero_of_eq
          rw [(F₂.truncatedFiltration_isBounded hbb₂ s₀).boundedAbove t
                (s + 1) (by change s₀ + 1 ≤ s + 1; omega),
            (F₂.truncatedFiltration_isBounded hbb₂ s₀).boundedAbove t
                s (by change s₀ + 1 ≤ s; omega)]
        exact unboundedExtensionPageIsoWithTop cm t (s, 0) ⊤ ≪≫
          IsZero.iso
            (SSData.eInfty_isZero_of_V
              (unboundedComplexSSData cm t s 0) hgrU)
            (SSData.eInfty_isZero_of_V
              ((truncatedUnderlyingComplex cm s₀ t).toSSData
                (truncatedUnderlyingComplex_isBounded cm hbb₁ hbb₂ s₀ t) s 0) hgrT)
    · have hgrU := unboundedUC_assocGraded_isZero_other cm t s k hk₁ hk₀
      have hgrT := truncatedUC_assocGraded_isZero_other cm s₀ t s k hk₁ hk₀
      exact unboundedExtensionPageIsoWithTop cm t (s, k) ⊤ ≪≫
        IsZero.iso
          (SSData.eInfty_isZero_of_V
            (unboundedComplexSSData cm t s k) hgrU)
          (SSData.eInfty_isZero_of_V
            ((truncatedUnderlyingComplex cm s₀ t).toSSData
              (truncatedUnderlyingComplex_isBounded cm hbb₁ hbb₂ s₀ t) s k) hgrT)

/-- 在有界下与 Mittag--Leffler 条件下，无界扩张弱收敛到最终常值截断复形的同调。 -/
theorem UnboundedExtensionSS.weakConvergence
    (cm : ConvergenceMorphism conv₁ conv₂)
    (hbb₁ : F₁.IsBoundedBelow) (hbb₂ : F₂.IsBoundedBelow)
    (hml₁ : F₁.IsMittagLeffler) (hml₂ : F₂.IsMittagLeffler) (t : ω') :
    ∃ (complexCompletion : FilteredComplex C),
      Nonempty (Convergence (UnboundedExtensionSS cm hbb₁ hbb₂ t)
        complexCompletion.homologyObj complexCompletion.homologyFiltration) := by
  obtain ⟨s₁, hs₁⟩ :=
    Filtration.eventually_constant_of_mittagLeffler F₁ hbb₁ hml₁ t
  obtain ⟨s₂, hs₂⟩ :=
    Filtration.eventually_constant_of_mittagLeffler F₂ hbb₂ hml₂ t
  let s₀ := max s₁ s₂
  have hstable₁ : ∀ q ≥ s₀, F₁.F q t = F₁.F s₀ t := by
    intro q hq
    rw [hs₁ q (le_trans (le_max_left _ _) hq),
      hs₁ s₀ (le_max_left _ _)]
  have hstable₂ : ∀ q ≥ s₀, F₂.F q t = F₂.F s₀ t := by
    intro q hq
    rw [hs₂ q (le_trans (le_max_right _ _) hq),
      hs₂ s₀ (le_max_right _ _)]
  let FC := truncatedUnderlyingComplex cm s₀ t
  let bnd := truncatedUnderlyingComplex_isBounded cm hbb₁ hbb₂ s₀ t
  let convT := FilteredComplex.weakConvergence FC bnd
  refine ⟨FC, ⟨{
    reindex := convT.reindex
    reindex_bijective := convT.reindex_bijective
    iso := fun sk =>
      UnboundedExtensionSS.eInftyIsoTruncated
        cm hbb₁ hbb₂ s₀ t hstable₁ hstable₂ sk.1 sk.2 ≪≫
      convT.iso sk }⟩⟩

end KIPBase.SpectralSequence
