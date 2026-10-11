/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import KIPBase.SpectralSequence.Commutativity
import KIPBase.SpectralSequence.UnboundedExtension

/-!
# 无界扩张谱序列的交换律

本文件把 `Commutativity` 中以有界过滤复形表述的 ESS 交换律推广到
`UnboundedExtensionSS`。这里的“无界”是指不再假设过滤有界；仍保留
`IsBoundedBelow`，因为它是无界扩张谱序列的收敛接口所需的单侧条件。

需要特别区分三个层次：

* 方块的四条边给出四个不同的扩张谱序列；
* 每条边的无界谱序列环境对象是原始谱序列的 `E∞` 项；
* 过滤复形的关联分次只通过收敛同构用于选择代表元，绝不替代环境对象。

因此不能仅凭逐页对象同构搬运第 2.12 条；还必须证明页微分关系与
未截断过滤复形代表元之间的相容性。下面先封装这层接口，再陈述并证明
无界交换律。
-/

namespace KIPBase.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v w w₀

set_option linter.dupNamespace false

variable {C : Type u} [Category.{v} C] [Abelian C]
variable [LocallySmall.{w₀} C] [WellPowered.{w₀} C]
variable [HasWidePullbacks.{w₀} C] [HasCoproducts.{w₀} C]

/-- 无界 ESS 在次数 `1` 的环境对象确实是源谱序列的原始 `E∞` 项。 -/
theorem unboundedExtension_source_V
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {ω' : Type w}
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    (cm : ConvergenceMorphism conv₁ conv₂)
    (hbb₁ : F₁.IsBoundedBelow) (hbb₂ : F₂.IsBoundedBelow)
    (t : ω') (s : ℤ) :
    ((UnboundedExtensionSS cm hbb₁ hbb₂ t).ssData (s, 1)).V =
      (E₁.ssData (conv₁.reindexEquiv.symm (s, t))).eInfty := by
  rfl

/-- 无界 ESS 在次数 `0` 的环境对象确实是目标谱序列的原始 `E∞` 项。 -/
theorem unboundedExtension_target_V
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {ω' : Type w}
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    (cm : ConvergenceMorphism conv₁ conv₂)
    (hbb₁ : F₁.IsBoundedBelow) (hbb₂ : F₂.IsBoundedBelow)
    (t : ω') (s : ℤ) :
    ((UnboundedExtensionSS cm hbb₁ hbb₂ t).ssData (s, 0)).V =
      (E₂.ssData (conv₂.reindexEquiv.symm (s, t))).eInfty := by
  rfl

/-! ## 无界微分关系的代表元接口 -/

/-- 无界 ESS 环境对象中的元素由未截断过滤复形中的元素表示。环境对象
本身仍是原始 `E∞` 项；这里只通过收敛同构比较它与关联分次。 -/
def UnboundedExtensionIsLift
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {ω' : Type w}
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω')
    (s k : ℤ) {T : C}
    (xl : T ⟶ Subobject.underlying.obj ((unboundedUnderlyingComplex cm t).fil s k))
    (x : T ⟶ (unboundedExtensionSSData cm t (s, k)).V) : Prop :=
  (unboundedUnderlyingComplex cm t).IsLift s k xl
    (x ≫ (unboundedExtensionVComplexIso cm t s k).hom)

/-- 同一源收敛谱序列发出的两条边，在次数 `1` 的提升条件一致。 -/
theorem unboundedExtensionIsLift_source_independent
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {ω' : Type w}
    {E₁ E₂ E₃ : SpectralSequence C ω}
    {A₁ A₂ A₃ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂} {F₃ : Filtration A₃}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {conv₃ : Convergence E₃ A₃ F₃}
    (cm₁ : ConvergenceMorphism conv₁ conv₂)
    (cm₂ : ConvergenceMorphism conv₁ conv₃) (t : ω') (s : ℤ)
    {T : C}
    (xl : T ⟶ Subobject.underlying.obj
      ((unboundedUnderlyingComplex cm₁ t).fil s 1))
    (x : T ⟶ (E₁.ssData (conv₁.reindexEquiv.symm (s, t))).eInfty)
    (h : UnboundedExtensionIsLift cm₁ t s 1 xl x) :
    UnboundedExtensionIsLift cm₂ t s 1 xl x := by
  unfold UnboundedExtensionIsLift at h ⊢
  rw [← unboundedExtensionVComplexIso_source_hom_eq cm₁ cm₂ t s]
  exact h

/-- 可复合两条边在公共顶点的提升条件一致。 -/
theorem unboundedExtensionIsLift_target_source
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {ω' : Type w}
    {E₁ E₂ E₃ : SpectralSequence C ω}
    {A₁ A₂ A₃ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂} {F₃ : Filtration A₃}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {conv₃ : Convergence E₃ A₃ F₃}
    (cm₁ : ConvergenceMorphism conv₁ conv₂)
    (cm₂ : ConvergenceMorphism conv₂ conv₃) (t : ω') (s : ℤ)
    {T : C}
    (xl : T ⟶ Subobject.underlying.obj
      ((unboundedUnderlyingComplex cm₁ t).fil s 0))
    (x : T ⟶ (E₂.ssData (conv₂.reindexEquiv.symm (s, t))).eInfty)
    (h : UnboundedExtensionIsLift cm₁ t s 0 xl x) :
    UnboundedExtensionIsLift cm₂ t s 1 xl x := by
  unfold UnboundedExtensionIsLift at h ⊢
  rw [← unboundedExtensionVComplexIso_target_source_hom_eq cm₁ cm₂ t s]
  exact h

/-- 同一目标收敛谱序列的两条边，在次数 `0` 的提升条件一致。 -/
theorem unboundedExtensionIsLift_target_independent
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {ω' : Type w}
    {E₀ E₁ E₂ : SpectralSequence C ω}
    {A₀ A₁ A₂ : ω' → C}
    {F₀ : Filtration A₀} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₀ : Convergence E₀ A₀ F₀} {conv₁ : Convergence E₁ A₁ F₁}
    {conv₂ : Convergence E₂ A₂ F₂}
    (cm₁ : ConvergenceMorphism conv₁ conv₂)
    (cm₂ : ConvergenceMorphism conv₀ conv₂) (t : ω') (s : ℤ)
    {T : C}
    (xl : T ⟶ Subobject.underlying.obj
      ((unboundedUnderlyingComplex cm₁ t).fil s 0))
    (x : T ⟶ (E₂.ssData (conv₂.reindexEquiv.symm (s, t))).eInfty)
    (h : UnboundedExtensionIsLift cm₁ t s 0 xl x) :
    UnboundedExtensionIsLift cm₂ t s 0 xl x := by
  unfold UnboundedExtensionIsLift at h ⊢
  rw [← unboundedExtensionVComplexIso_target_hom_eq cm₁ cm₂ t s]
  exact h

/-- 未截断两项复形中的过滤微分等式可送到极限对象中的实际映射等式。 -/
theorem unbounded_lift_ambient_map
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {ω' : Type w}
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω')
    (s u : ℤ) (hsu : s ≤ u) {T : C}
    (xl : T ⟶ Subobject.underlying.obj
      ((unboundedUnderlyingComplex cm t).fil s 1))
    (yl : T ⟶ Subobject.underlying.obj
      ((unboundedUnderlyingComplex cm t).fil u 0))
    (hd : xl ≫ (unboundedUnderlyingComplex cm t).filDiff s 1 =
      yl ≫ Subobject.ofLE
        ((unboundedUnderlyingComplex cm t).fil u 0)
        ((unboundedUnderlyingComplex cm t).fil s 0)
        ((unboundedUnderlyingComplex cm t).fil_anti_of_le 0 hsu)) :
    xl ≫ ((unboundedUnderlyingComplex cm t).fil s 1).arrow ≫ cm.aMap t =
      yl ≫ ((unboundedUnderlyingComplex cm t).fil u 0).arrow := by
  have hmap : (unboundedUnderlyingComplex cm t).d 1 = cm.aMap t := by
    simp [unboundedUnderlyingComplex, underlyingComplex,
      twoTermDiff, twoTermObj]
  have hfil := (unboundedUnderlyingComplex cm t).filDiff_comp_arrow s 1
  change (unboundedUnderlyingComplex cm t).filDiff s 1 ≫
      ((unboundedUnderlyingComplex cm t).fil s 0).arrow =
    ((unboundedUnderlyingComplex cm t).fil s 1).arrow ≫
      (unboundedUnderlyingComplex cm t).d 1 at hfil
  have hcore : xl ≫ ((unboundedUnderlyingComplex cm t).fil s 1).arrow ≫
      cm.aMap t =
      (xl ≫ (unboundedUnderlyingComplex cm t).filDiff s 1) ≫
        ((unboundedUnderlyingComplex cm t).fil s 0).arrow := by
    simpa [Category.assoc, unboundedUnderlyingComplex, underlyingComplex,
      twoTermDiff, twoTermObj] using
        congrArg (fun f => xl ≫ f) hfil.symm
  have htail :
      (xl ≫ (unboundedUnderlyingComplex cm t).filDiff s 1) ≫
          ((unboundedUnderlyingComplex cm t).fil s 0).arrow =
        yl ≫ ((unboundedUnderlyingComplex cm t).fil u 0).arrow := by
    simpa [Category.assoc, unboundedUnderlyingComplex, underlyingComplex,
      twoTermFil, twoTermObj] using congrArg
        (fun f => f ≫ ((unboundedUnderlyingComplex cm t).fil s 0).arrow) hd
  exact hcore.trans htail

/-- 若次数 `1` 与次数 `0` 的环境映射在两项复形中相等，则该等式唯一提升为
过滤微分等式。证明只使用目标过滤子对象箭头的单态性。 -/
theorem unbounded_filDiff_of_ambient_map
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {ω' : Type w}
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω')
    (s u : ℤ) (hsu : s ≤ u) {T : C}
    (xl : T ⟶ Subobject.underlying.obj
      ((unboundedUnderlyingComplex cm t).fil s 1))
    (yl : T ⟶ Subobject.underlying.obj
      ((unboundedUnderlyingComplex cm t).fil u 0))
    (ha : xl ≫ ((unboundedUnderlyingComplex cm t).fil s 1).arrow ≫
        cm.aMap t =
      yl ≫ ((unboundedUnderlyingComplex cm t).fil u 0).arrow) :
    xl ≫ (unboundedUnderlyingComplex cm t).filDiff s 1 =
      yl ≫ Subobject.ofLE
        ((unboundedUnderlyingComplex cm t).fil u 0)
        ((unboundedUnderlyingComplex cm t).fil s 0)
        ((unboundedUnderlyingComplex cm t).fil_anti_of_le 0 hsu) := by
  let FC := unboundedUnderlyingComplex cm t
  have hdiff := FC.filDiff_comp_arrow s 1
  change FC.filDiff s 1 ≫ (FC.fil s 0).arrow =
    (FC.fil s 1).arrow ≫ FC.d 1 at hdiff
  apply (cancel_mono (FC.fil s 0).arrow).mp
  have hcore : (xl ≫ FC.filDiff s 1) ≫ (FC.fil s 0).arrow =
      xl ≫ (FC.fil s 1).arrow ≫ cm.aMap t := by
    simpa [FC, Category.assoc, unboundedUnderlyingComplex,
      underlyingComplex, twoTermDiff, twoTermObj] using
        congrArg (fun f => xl ≫ f) hdiff
  have ha' : xl ≫ (FC.fil s 1).arrow ≫ cm.aMap t =
      yl ≫ (FC.fil u 0).arrow := by
    simpa only [FC] using ha
  have htail : yl ≫ (FC.fil u 0).arrow =
      (yl ≫ Subobject.ofLE (FC.fil u 0) (FC.fil s 0)
        (FC.fil_anti_of_le 0 hsu)) ≫ (FC.fil s 0).arrow := by
    simpa only [Category.assoc] using congrArg (fun f => yl ≫ f)
      (Subobject.ofLE_arrow (FC.fil_anti_of_le 0 hsu)).symm
  exact hcore.trans (ha'.trans htail)

/-- 未截断过滤复形中的严格微分等式产生无界 ESS 的微分关系。此定理
直接使用无界谱序列的有限 `Z/B` 塔与共轭微分，不经过任何有界截断。 -/
theorem unboundedDifferentialRelation_of_lift
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {ω' : Type w}
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω')
    (r : ℤ) (hr : 0 ≤ r) (s k : ℤ) {T : C}
    {x : T ⟶ (unboundedExtensionSSData cm t (s, k)).V}
    {y : T ⟶ (unboundedExtensionSSData cm t (s + r, k - 1)).V}
    {xl : T ⟶ Subobject.underlying.obj ((unboundedUnderlyingComplex cm t).fil s k)}
    {yl : T ⟶ Subobject.underlying.obj
      ((unboundedUnderlyingComplex cm t).fil (s + r) (k - 1))}
    (hx : UnboundedExtensionIsLift cm t s k xl x)
    (hy : UnboundedExtensionIsLift cm t (s + r) (k - 1) yl y)
    (hd : xl ≫ (unboundedUnderlyingComplex cm t).filDiff s k =
      yl ≫ Subobject.ofLE
        ((unboundedUnderlyingComplex cm t).fil (s + r) (k - 1))
        ((unboundedUnderlyingComplex cm t).fil s (k - 1))
        ((unboundedUnderlyingComplex cm t).fil_anti_of_le (k - 1) (by omega))) :
    DifferentialRelation (ExtensionSpectralSequence cm t) r (s, k) x y := by
  classical
  unfold UnboundedExtensionIsLift FilteredComplex.IsLift at hx hy
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hr
  let FC := unboundedUnderlyingComplex cm t
  let xC : T ⟶ Subobject.underlying.obj
      ((unboundedComplexSSDataFamily cm t (s, k)).Z (n : WithTop ℕ)) :=
    unboundedComplexSourceCycleLift cm t s k n hd
  let yC : T ⟶ Subobject.underlying.obj
      ((unboundedComplexSSDataFamily cm t (s + (n : ℤ), k - 1)).Z
        (n : WithTop ℕ)) :=
    unboundedComplexTargetCycleLift cm t s k n hd
  let xZ := xC ≫ (unboundedExtensionZIso cm t (s, k) (n : WithTop ℕ)).inv
  let yZ := yC ≫
    (unboundedExtensionZIso cm t (s + (n : ℤ), k - 1) (n : WithTop ℕ)).inv
  unfold DifferentialRelation
  dsimp only [ExtensionSpectralSequence_r₀, sub_zero, Int.toNat_natCast,
    ExtensionSpectralSequence_diffDeg]
  refine ⟨xZ, ?_, yZ, ?_, ?_⟩
  · change xZ ≫ ((unboundedExtensionSSData cm t (s, k)).Z
        (n : WithTop ℕ)).arrow = x
    have hxC : xC ≫ ((unboundedComplexSSDataFamily cm t (s, k)).Z
        (n : WithTop ℕ)).arrow =
        x ≫ (unboundedSSDataForward cm t).φ (s, k) := by
      dsimp only [xC]
      rw [unboundedComplexSourceCycleLift_arrow]
      change @Eq (T ⟶ (unboundedComplexSSDataFamily cm t (s, k)).V)
        (xl ≫ (unboundedUnderlyingComplex cm t).filToAssocGraded s k)
        (x ≫ (unboundedSSDataForward cm t).φ (s, k)) at hx
      exact hx
    have hback := (unboundedSSDataBackward cm t).preserves_Z
      (s, k) (n : WithTop ℕ) |>.choose_spec
    have hcancel : (unboundedSSDataForward cm t).φ (s, k) ≫
        (unboundedSSDataBackward cm t).φ (s, k) =
        𝟙 ((unboundedExtensionSSData cm t (s, k)).V) := by
      change (unboundedExtensionVComplexIso cm t s k).hom ≫
        (unboundedExtensionVComplexIso cm t s k).inv = 𝟙 _
      exact (unboundedExtensionVComplexIso cm t s k).hom_inv_id
    dsimp only [xZ, unboundedExtensionZIso]
    rw [Category.assoc, hback, ← Category.assoc, hxC,
      Category.assoc, hcancel, Category.comp_id]
  · change yZ ≫ ((unboundedExtensionSSData cm t
        (s + (n : ℤ), k - 1)).Z (n : WithTop ℕ)).arrow = y
    have hyC : yC ≫ ((unboundedComplexSSDataFamily cm t
        (s + (n : ℤ), k - 1)).Z (n : WithTop ℕ)).arrow =
        y ≫ (unboundedSSDataForward cm t).φ
          (s + (n : ℤ), k - 1) := by
      dsimp only [yC]
      rw [unboundedComplexTargetCycleLift_arrow]
      change @Eq (T ⟶ (unboundedComplexSSDataFamily cm t
          (s + (n : ℤ), k - 1)).V)
        (yl ≫ (unboundedUnderlyingComplex cm t).filToAssocGraded
          (s + (n : ℤ)) (k - 1))
        (y ≫ (unboundedSSDataForward cm t).φ
          (s + (n : ℤ), k - 1)) at hy
      exact hy
    have hback := (unboundedSSDataBackward cm t).preserves_Z
      (s + (n : ℤ), k - 1) (n : WithTop ℕ) |>.choose_spec
    have hcancel : (unboundedSSDataForward cm t).φ
          (s + (n : ℤ), k - 1) ≫
        (unboundedSSDataBackward cm t).φ
          (s + (n : ℤ), k - 1) =
        𝟙 ((unboundedExtensionSSData cm t
          (s + (n : ℤ), k - 1)).V) := by
      change (unboundedExtensionVComplexIso cm t
          (s + (n : ℤ)) (k - 1)).hom ≫
        (unboundedExtensionVComplexIso cm t
          (s + (n : ℤ)) (k - 1)).inv = 𝟙 _
      exact (unboundedExtensionVComplexIso cm t
        (s + (n : ℤ)) (k - 1)).hom_inv_id
    dsimp only [yZ, unboundedExtensionZIso]
    rw [Category.assoc, hback, ← Category.assoc, hyC,
      Category.assoc, hcancel, Category.comp_id]
  · rw [ExtensionSpectralSequence_d_nat]
    change xZ ≫ (unboundedExtensionSSData cm t (s, k)).pageπ (n : WithTop ℕ) ≫
        unboundedExtensionDifferential cm t s k n =
      yZ ≫ (unboundedExtensionSSData cm t (s + (n : ℤ), k - 1)).pageπ
        (n : WithTop ℕ)
    dsimp only [xZ, yZ]
    simp only [Category.assoc]
    rw [← Category.assoc
        (unboundedExtensionZIso cm t (s, k) (n : WithTop ℕ)).inv,
      unboundedExtensionZIso_inv_pageπ_nat, unboundedExtensionDifferential]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [unboundedExtensionZIso_inv_pageπ_nat]
    apply (cancel_mono (unboundedExtensionPageIso cm t
      (s + (n : ℤ), k - 1) n).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    change xC ≫ FC.finitePageπ s k n ≫ FC.finitePageDifferential s k n =
      yC ≫ FC.finitePageπ (s + (n : ℤ)) (k - 1) n
    dsimp only [xC, yC]
    exact FC.finitePageDifferential_of_lift s k n hd

/-- 严格提升定理的显式目标过滤次数版本。 -/
theorem unboundedDifferentialRelation_of_lift_at_target
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {ω' : Type w}
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω')
    (r : ℤ) (hr : 0 ≤ r) (s u k : ℤ) (hsu : s + r = u) {T : C}
    {x : T ⟶ (unboundedExtensionSSData cm t (s, k)).V}
    {y : T ⟶ (unboundedExtensionSSData cm t (u, k - 1)).V}
    {xl : T ⟶ Subobject.underlying.obj
      ((unboundedUnderlyingComplex cm t).fil s k)}
    {yl : T ⟶ Subobject.underlying.obj
      ((unboundedUnderlyingComplex cm t).fil u (k - 1))}
    (hx : UnboundedExtensionIsLift cm t s k xl x)
    (hy : UnboundedExtensionIsLift cm t u (k - 1) yl y)
    (hd : xl ≫ (unboundedUnderlyingComplex cm t).filDiff s k =
      yl ≫ Subobject.ofLE
        ((unboundedUnderlyingComplex cm t).fil u (k - 1))
        ((unboundedUnderlyingComplex cm t).fil s (k - 1))
        ((unboundedUnderlyingComplex cm t).fil_anti_of_le (k - 1) (by omega))) :
    DifferentialRelation (ExtensionSpectralSequence cm t) r (s, k) x
      (Eq.mpr (congrArg (fun X : C => T ⟶ X)
        (show ((ExtensionSpectralSequence cm t).ssData
          ((s, k) + (ExtensionSpectralSequence cm t).diffDeg r)).V =
          (unboundedExtensionSSData cm t (u, k - 1)).V by
            rw [← hsu]
            rfl)) y) := by
  subst u
  exact unboundedDifferentialRelation_of_lift cm t r hr s k hx hy hd

/-- 反过来，极限对象中的实际映射等式连同两端提升产生无界 ESS 关系。 -/
theorem unboundedDifferentialRelation_of_ambient_map
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {ω' : Type w}
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω')
    (r : ℤ) (hr : 0 ≤ r) (s u : ℤ) (hsu : s + r = u) {T : C}
    {x : T ⟶ (unboundedExtensionSSData cm t (s, 1)).V}
    {y : T ⟶ (unboundedExtensionSSData cm t (u, 0)).V}
    (xl : T ⟶ Subobject.underlying.obj
      ((unboundedUnderlyingComplex cm t).fil s 1))
    (yl : T ⟶ Subobject.underlying.obj
      ((unboundedUnderlyingComplex cm t).fil u 0))
    (hx : UnboundedExtensionIsLift cm t s 1 xl x)
    (hy : UnboundedExtensionIsLift cm t u 0 yl y)
    (ha : xl ≫ ((unboundedUnderlyingComplex cm t).fil s 1).arrow ≫
        cm.aMap t =
      yl ≫ ((unboundedUnderlyingComplex cm t).fil u 0).arrow) :
    DifferentialRelation (ExtensionSpectralSequence cm t) r (s, 1) x
      (Eq.mpr (congrArg (fun X : C => T ⟶ X)
        (show ((ExtensionSpectralSequence cm t).ssData
          ((s, 1) + (ExtensionSpectralSequence cm t).diffDeg r)).V =
          (unboundedExtensionSSData cm t (u, 0)).V by
            rw [← hsu]
            rfl)) y) := by
  let FC := unboundedUnderlyingComplex cm t
  have hfil : xl ≫ FC.filDiff s 1 =
      yl ≫ Subobject.ofLE (FC.fil u 0) (FC.fil s 0)
        (FC.fil_anti_of_le 0 (by omega)) :=
    unbounded_filDiff_of_ambient_map cm t s u (by omega) xl yl ha
  exact unboundedDifferentialRelation_of_lift_at_target cm t
    r hr s u 1 hsu hx hy hfil

/-- 无界 ESS 微分关系的两端可提升到未截断过滤复形；源提升的实际微分
另记为 `yd`。指定目标与 `yd` 的差将在下一条定理中用有限边缘层修正。 -/
theorem unbounded_lift_endpoints_of_differentialRelation
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {ω' : Type w}
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω')
    (r : ℤ) (hr : 0 ≤ r) (s k : ℤ) {T : C} [Projective T]
    {x : T ⟶ (unboundedExtensionSSData cm t (s, k)).V}
    {y : T ⟶ (unboundedExtensionSSData cm t (s + r, k - 1)).V}
    (h : DifferentialRelation (ExtensionSpectralSequence cm t) r (s, k) x y) :
    ∃ (xl : T ⟶ Subobject.underlying.obj
          ((unboundedUnderlyingComplex cm t).fil s k))
      (yl yd : T ⟶ Subobject.underlying.obj
          ((unboundedUnderlyingComplex cm t).fil (s + r) (k - 1))),
      UnboundedExtensionIsLift cm t s k xl x ∧
      UnboundedExtensionIsLift cm t (s + r) (k - 1) yl y ∧
      xl ≫ (unboundedUnderlyingComplex cm t).filDiff s k =
        yd ≫ Subobject.ofLE
          ((unboundedUnderlyingComplex cm t).fil (s + r) (k - 1))
          ((unboundedUnderlyingComplex cm t).fil s (k - 1))
          ((unboundedUnderlyingComplex cm t).fil_anti_of_le (k - 1) (by omega)) := by
  classical
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hr
  unfold DifferentialRelation at h
  dsimp only [ExtensionSpectralSequence_r₀, sub_zero, Int.toNat_natCast,
    ExtensionSpectralSequence_diffDeg] at h
  rw [ExtensionSpectralSequence_d_nat] at h
  change ∃ (xZ : T ⟶ Subobject.underlying.obj
      ((unboundedExtensionSSData cm t (s, k)).Z (n : WithTop ℕ))),
      xZ ≫ ((unboundedExtensionSSData cm t (s, k)).Z
          (n : WithTop ℕ)).arrow = x ∧
      ∃ (yZ : T ⟶ Subobject.underlying.obj
        ((unboundedExtensionSSData cm t
          (s + (n : ℤ), k - 1)).Z (n : WithTop ℕ))),
        yZ ≫ ((unboundedExtensionSSData cm t
            (s + (n : ℤ), k - 1)).Z (n : WithTop ℕ)).arrow = y ∧
        xZ ≫ (unboundedExtensionSSData cm t (s, k)).pageπ
              (n : WithTop ℕ) ≫
            unboundedExtensionDifferential cm t s k n =
          yZ ≫ (unboundedExtensionSSData cm t
            (s + (n : ℤ), k - 1)).pageπ (n : WithTop ℕ) at h
  rcases h with ⟨xZ, hxZ, yZ, hyZ, _hpage⟩
  let FC := unboundedUnderlyingComplex cm t
  let xC := xZ ≫ (unboundedExtensionZIso cm t (s, k) (n : WithTop ℕ)).hom
  let yC := yZ ≫
    (unboundedExtensionZIso cm t (s + (n : ℤ), k - 1) (n : WithTop ℕ)).hom
  let f := (FC.fil s k).arrow ≫ FC.d k ≫
    cokernel.π ((FC.fil (s + (n : ℤ)) (k - 1)).arrow)
  let g := (FC.fil (s + (n : ℤ)) (k - 1)).arrow ≫ FC.d (k - 1) ≫
    cokernel.π ((FC.fil (s + (n : ℤ) + (n : ℤ)) (k - 1 - 1)).arrow)
  let K := kernelSubobject f
  let K' := kernelSubobject g
  let p := factorThruImageSubobject (K.arrow ≫ FC.filToAssocGraded s k)
  let q := factorThruImageSubobject
    (K'.arrow ≫ FC.filToAssocGraded (s + (n : ℤ)) (k - 1))
  let xC' : T ⟶ Subobject.underlying.obj
      (imageSubobject (K.arrow ≫ FC.filToAssocGraded s k)) := by
    change T ⟶ Subobject.underlying.obj
      ((unboundedComplexSSDataFamily cm t (s, k)).Z (n : WithTop ℕ))
    exact xC
  let yC' : T ⟶ Subobject.underlying.obj
      (imageSubobject
        (K'.arrow ≫ FC.filToAssocGraded (s + (n : ℤ)) (k - 1))) := by
    change T ⟶ Subobject.underlying.obj
      ((unboundedComplexSSDataFamily cm t
        (s + (n : ℤ), k - 1)).Z (n : WithTop ℕ))
    exact yC
  let u := Projective.factorThru xC' p
  let v := Projective.factorThru yC' q
  have hxC' : xC' ≫ (imageSubobject
      (K.arrow ≫ FC.filToAssocGraded s k)).arrow =
      x ≫ (unboundedExtensionVComplexIso cm t s k).hom := by
    have hcompat := congrArg (fun f => xZ ≫ f)
      (unboundedExtensionZIso_hom_arrow cm t s k (n : WithTop ℕ))
    change xZ ≫ (unboundedExtensionZIso cm t (s, k)
        (n : WithTop ℕ)).hom ≫
          ((unboundedUnderlyingComplex cm t).cycleSubobject s k
            (n : WithTop ℕ)).arrow = _ at hcompat
    have hcompat' := (Category.assoc xZ
      (unboundedExtensionZIso cm t (s, k) (n : WithTop ℕ)).hom
      ((unboundedUnderlyingComplex cm t).cycleSubobject s k
        (n : WithTop ℕ)).arrow).trans hcompat
    have hcompat'' := hcompat'.trans (Category.assoc xZ
      ((unboundedExtensionSSData cm t (s, k)).Z
        (n : WithTop ℕ)).arrow
      (unboundedExtensionVComplexIso cm t s k).hom).symm
    have hleft : xC' ≫ (imageSubobject
        (K.arrow ≫ FC.filToAssocGraded s k)).arrow =
        (xZ ≫ ((unboundedExtensionSSData cm t (s, k)).Z
          (n : WithTop ℕ)).arrow) ≫
            (unboundedExtensionVComplexIso cm t s k).hom := by
      dsimp only [xC', xC]
      exact hcompat''
    exact hleft.trans (congrArg (fun f => f ≫
      (unboundedExtensionVComplexIso cm t s k).hom) hxZ)
  have hyC' : yC' ≫ (imageSubobject
      (K'.arrow ≫ FC.filToAssocGraded (s + (n : ℤ)) (k - 1))).arrow =
      y ≫ (unboundedExtensionVComplexIso cm t
        (s + (n : ℤ)) (k - 1)).hom := by
    have hcompat := congrArg (fun f => yZ ≫ f)
      (unboundedExtensionZIso_hom_arrow cm t
        (s + (n : ℤ)) (k - 1) (n : WithTop ℕ))
    change yZ ≫ (unboundedExtensionZIso cm t
        (s + (n : ℤ), k - 1) (n : WithTop ℕ)).hom ≫
          ((unboundedUnderlyingComplex cm t).cycleSubobject
            (s + (n : ℤ)) (k - 1) (n : WithTop ℕ)).arrow = _ at hcompat
    have hcompat' := (Category.assoc yZ
      (unboundedExtensionZIso cm t
        (s + (n : ℤ), k - 1) (n : WithTop ℕ)).hom
      ((unboundedUnderlyingComplex cm t).cycleSubobject
        (s + (n : ℤ)) (k - 1) (n : WithTop ℕ)).arrow).trans hcompat
    have hcompat'' := hcompat'.trans (Category.assoc yZ
      ((unboundedExtensionSSData cm t
        (s + (n : ℤ), k - 1)).Z (n : WithTop ℕ)).arrow
      (unboundedExtensionVComplexIso cm t
        (s + (n : ℤ)) (k - 1)).hom).symm
    have hleft : yC' ≫ (imageSubobject
        (K'.arrow ≫ FC.filToAssocGraded
          (s + (n : ℤ)) (k - 1))).arrow =
        (yZ ≫ ((unboundedExtensionSSData cm t
          (s + (n : ℤ), k - 1)).Z (n : WithTop ℕ)).arrow) ≫
            (unboundedExtensionVComplexIso cm t
              (s + (n : ℤ)) (k - 1)).hom := by
      dsimp only [yC', yC]
      exact hcompat''
    exact hleft.trans (congrArg (fun f => f ≫
      (unboundedExtensionVComplexIso cm t
        (s + (n : ℤ)) (k - 1)).hom) hyZ)
  have hdK : (K.arrow ≫ (FC.fil s k).arrow ≫ FC.d k) ≫
      cokernel.π ((FC.fil (s + (n : ℤ)) (k - 1)).arrow) = 0 := by
    simpa only [f, Category.assoc] using kernelSubobject_arrow_comp f
  let dLift := Abelian.monoLift (FC.fil (s + (n : ℤ)) (k - 1)).arrow
    (K.arrow ≫ (FC.fil s k).arrow ≫ FC.d k) hdK
  refine ⟨u ≫ K.arrow, v ≫ K'.arrow, u ≫ dLift, ?_, ?_, ?_⟩
  · unfold UnboundedExtensionIsLift
    change (u ≫ K.arrow) ≫ FC.filToAssocGraded s k =
      x ≫ (unboundedExtensionVComplexIso cm t s k).hom
    calc
      (u ≫ K.arrow) ≫ FC.filToAssocGraded s k =
          u ≫ (K.arrow ≫ FC.filToAssocGraded s k) := Category.assoc _ _ _
      _ = (u ≫ p) ≫ (imageSubobject
          (K.arrow ≫ FC.filToAssocGraded s k)).arrow := by
            rw [Category.assoc, imageSubobject_arrow_comp]
      _ = xC' ≫ (imageSubobject
          (K.arrow ≫ FC.filToAssocGraded s k)).arrow := by
            rw [Projective.factorThru_comp]
      _ = x ≫ (unboundedExtensionVComplexIso cm t s k).hom := hxC'
  · unfold UnboundedExtensionIsLift
    change (v ≫ K'.arrow) ≫ FC.filToAssocGraded (s + (n : ℤ)) (k - 1) =
      y ≫ (unboundedExtensionVComplexIso cm t (s + (n : ℤ)) (k - 1)).hom
    calc
      (v ≫ K'.arrow) ≫ FC.filToAssocGraded (s + (n : ℤ)) (k - 1) =
          v ≫ (K'.arrow ≫
            FC.filToAssocGraded (s + (n : ℤ)) (k - 1)) := Category.assoc _ _ _
      _ = (v ≫ q) ≫ (imageSubobject
          (K'.arrow ≫ FC.filToAssocGraded
            (s + (n : ℤ)) (k - 1))).arrow := by
            rw [Category.assoc, imageSubobject_arrow_comp]
      _ = yC' ≫ (imageSubobject
          (K'.arrow ≫ FC.filToAssocGraded
            (s + (n : ℤ)) (k - 1))).arrow := by
            rw [Projective.factorThru_comp]
      _ = y ≫ (unboundedExtensionVComplexIso cm t
              (s + (n : ℤ)) (k - 1)).hom := hyC'
  · apply (cancel_mono (FC.fil s (k - 1)).arrow).mp
    change ((u ≫ K.arrow) ≫ FC.filDiff s k) ≫
        (FC.fil s (k - 1)).arrow =
      ((u ≫ dLift) ≫ Subobject.ofLE
        (FC.fil (s + (n : ℤ)) (k - 1)) (FC.fil s (k - 1)) _) ≫
          (FC.fil s (k - 1)).arrow
    simp only [Category.assoc, FC.filDiff_comp_arrow,
      Subobject.ofLE_arrow, dLift, Abelian.monoLift_comp]

/-- 无界 ESS 的 `d_r` 关系可完整提升到未截断过滤复形。投射性先提升
有限循环层见证，再把实际目标与指定目标之差沿有限边缘层提升并修正。 -/
theorem unbounded_lift_of_differentialRelation
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {ω' : Type w}
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω')
    (r : ℤ) (hr : 0 ≤ r) (s k : ℤ) {T : C} [Projective T]
    {x : T ⟶ (unboundedExtensionSSData cm t (s, k)).V}
    {y : T ⟶ (unboundedExtensionSSData cm t (s + r, k - 1)).V}
    (h : DifferentialRelation (ExtensionSpectralSequence cm t) r (s, k) x y) :
    ∃ (xl : T ⟶ Subobject.underlying.obj
          ((unboundedUnderlyingComplex cm t).fil s k))
      (yl : T ⟶ Subobject.underlying.obj
          ((unboundedUnderlyingComplex cm t).fil (s + r) (k - 1))),
      UnboundedExtensionIsLift cm t s k xl x ∧
      UnboundedExtensionIsLift cm t (s + r) (k - 1) yl y ∧
      xl ≫ (unboundedUnderlyingComplex cm t).filDiff s k =
        yl ≫ Subobject.ofLE
          ((unboundedUnderlyingComplex cm t).fil (s + r) (k - 1))
          ((unboundedUnderlyingComplex cm t).fil s (k - 1))
          ((unboundedUnderlyingComplex cm t).fil_anti_of_le (k - 1) (by omega)) := by
  classical
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hr
  let FC := unboundedUnderlyingComplex cm t
  obtain ⟨xl, yl, yd, hx, hy, hd⟩ :=
    unbounded_lift_endpoints_of_differentialRelation cm t (n : ℤ)
      (Int.natCast_nonneg n) s k h
  let y₀C := yd ≫ FC.filToAssocGraded (s + (n : ℤ)) (k - 1)
  let y₀ : T ⟶ (unboundedExtensionSSData cm t
      (s + (n : ℤ), k - 1)).V := y₀C ≫
    (unboundedExtensionVComplexIso cm t (s + (n : ℤ)) (k - 1)).inv
  have hy₀ : UnboundedExtensionIsLift cm t
      (s + (n : ℤ)) (k - 1) yd y₀ := by
    unfold UnboundedExtensionIsLift
    dsimp only [y₀, y₀C]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl
  have h₀ : DifferentialRelation (ExtensionSpectralSequence cm t)
      (n : ℤ) (s, k) x y₀ :=
    unboundedDifferentialRelation_of_lift cm t (n : ℤ)
      (Int.natCast_nonneg n) s k hx hy₀ hd
  have hboundary := DifferentialRelation.targets_sub_factors_boundary
    (ExtensionSpectralSequence cm t) (n : ℤ) (s, k) h₀ h
  change Subobject.Factors
    ((unboundedExtensionSSData cm t
      (s + (n : ℤ), k - 1)).B (n : WithTop ℕ)) (y₀ - y) at hboundary
  have hboundaryC : Subobject.Factors
      (FC.boundarySubobject (s + (n : ℤ)) (k - 1) (n : WithTop ℕ))
      (y₀C - y ≫
        (unboundedExtensionVComplexIso cm t (s + (n : ℤ)) (k - 1)).hom) := by
    change Subobject.Factors
      ((unboundedComplexSSDataFamily cm t
        (s + (n : ℤ), k - 1)).B (n : WithTop ℕ))
      (y₀C - y ≫
        (unboundedExtensionVComplexIso cm t (s + (n : ℤ)) (k - 1)).hom)
    have hy₀map : y₀ ≫
        (unboundedExtensionVComplexIso cm t
          (s + (n : ℤ)) (k - 1)).hom = y₀C := by
      dsimp only [y₀, y₀C]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have hf := unboundedExtension_boundary_factors_forward cm t
      (s + (n : ℤ)) (k - 1) (n : WithTop ℕ) hboundary
    rw [Preadditive.sub_comp] at hf
    change Subobject.Factors
      ((unboundedComplexSSDataFamily cm t
        (s + (n : ℤ), k - 1)).B (n : WithTop ℕ))
      (y₀ ≫ (unboundedExtensionVComplexIso cm t
        (s + (n : ℤ)) (k - 1)).hom -
        y ≫ (unboundedExtensionVComplexIso cm t
          (s + (n : ℤ)) (k - 1)).hom) at hf
    rw [hy₀map] at hf
    exact hf
  obtain ⟨a, b, hdb', hbb⟩ :=
    FC.lift_boundary_at_differential s k n hboundaryC
  let i := Subobject.ofLE (FC.fil (s + 1) k) (FC.fil s k) (FC.fil_anti s k)
  let j := Subobject.ofLE (FC.fil (s + (n : ℤ)) (k - 1))
    (FC.fil s (k - 1)) (FC.fil_anti_of_le (k - 1) (by omega))
  let xl' := xl - a ≫ i
  let yl' := yd - b
  have hdFC : xl ≫ FC.filDiff s k = yd ≫ j := by
    simpa only [FC, j] using hd
  have ha : (a ≫ i) ≫ FC.filDiff s k = b ≫ j := by
    apply (cancel_mono (FC.fil s (k - 1)).arrow).mp
    calc
      ((a ≫ i) ≫ FC.filDiff s k) ≫ (FC.fil s (k - 1)).arrow =
          a ≫ (FC.fil (s + 1) k).arrow ≫ FC.d k := by
            rw [Category.assoc, FC.filDiff_comp_arrow]
            simpa only [Category.assoc] using
              congrArg (fun q => q ≫ FC.d k)
                (by simp only [i, Category.assoc, Subobject.ofLE_arrow] :
                  (a ≫ i) ≫ (FC.fil s k).arrow =
                    a ≫ (FC.fil (s + 1) k).arrow)
      _ = b ≫ (FC.fil (s + (n : ℤ)) (k - 1)).arrow := hdb'
      _ = (b ≫ j) ≫ (FC.fil s (k - 1)).arrow := by
        simp only [Category.assoc, j, Subobject.ofLE_arrow]
  refine ⟨xl', yl', ?_, ?_, ?_⟩
  · unfold UnboundedExtensionIsLift at hx ⊢
    change xl' ≫ FC.filToAssocGraded s k =
      x ≫ (unboundedExtensionVComplexIso cm t s k).hom
    have hzero : (a ≫ i) ≫ FC.filToAssocGraded s k = 0 := by
      change (a ≫ i) ≫ cokernel.π i = 0
      rw [Category.assoc, cokernel.condition, comp_zero]
    change xl ≫ FC.filToAssocGraded s k =
      x ≫ (unboundedExtensionVComplexIso cm t s k).hom at hx
    simpa only [xl', Preadditive.sub_comp, hzero, sub_zero] using hx
  · unfold UnboundedExtensionIsLift
    change yl' ≫ FC.filToAssocGraded (s + (n : ℤ)) (k - 1) =
      y ≫ (unboundedExtensionVComplexIso cm t
        (s + (n : ℤ)) (k - 1)).hom
    simp only [yl', Preadditive.sub_comp, hbb, y₀C]
    abel
  · change xl' ≫ FC.filDiff s k = yl' ≫ j
    simp only [xl', yl', Preadditive.sub_comp, hdFC, ha]

/-- The degree-one specialization of `unbounded_lift_of_differentialRelation`,
with the target complex degree normalized before specialization. -/
theorem unbounded_lift_of_differentialRelation_one
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {ω' : Type w}
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω')
    (r : ℤ) (hr : 0 ≤ r) (s : ℤ) {T : C} [Projective T]
    {x : T ⟶ (unboundedExtensionSSData cm t (s, 1)).V}
    {y : T ⟶ (unboundedExtensionSSData cm t (s + r, 0)).V}
    (h : DifferentialRelation (ExtensionSpectralSequence cm t) r (s, 1) x y) :
    ∃ (xl : T ⟶ Subobject.underlying.obj
          ((unboundedUnderlyingComplex cm t).fil s 1))
      (yl : T ⟶ Subobject.underlying.obj
          ((unboundedUnderlyingComplex cm t).fil (s + r) 0)),
      UnboundedExtensionIsLift cm t s 1 xl x ∧
      UnboundedExtensionIsLift cm t (s + r) 0 yl y ∧
      xl ≫ (unboundedUnderlyingComplex cm t).filDiff s 1 =
        yl ≫ Subobject.ofLE
          ((unboundedUnderlyingComplex cm t).fil (s + r) 0)
          ((unboundedUnderlyingComplex cm t).fil s 0)
          ((unboundedUnderlyingComplex cm t).fil_anti_of_le 0 (by omega)) := by
  obtain ⟨xl, yl, hx, hy, hd⟩ :=
    unbounded_lift_of_differentialRelation cm t r hr s 1 h
  refine ⟨xl, yl, hx, ?_, ?_⟩
  · norm_num at hy ⊢
    exact hy
  · norm_num at hd ⊢
    exact hd

/-! ## 无界 crossing 的复形代表元接口 -/

/-- 把未截断复形关联分次中的广义元素搬回无界 ESS 的原始 `E∞` 环境。 -/
noncomputable def UnboundedExtensionClass
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {ω' : Type w}
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω')
    (s k : ℤ) {T : C}
    (a : T ⟶ (unboundedUnderlyingComplex cm t).assocGraded s k) :
    T ⟶ (unboundedExtensionSSData cm t (s, k)).V :=
  a ≫ (unboundedExtensionVComplexIso cm t s k).inv

/-- 未截断复形中的非边缘严格微分给出无界 ESS 的本质微分关系。 -/
theorem unbounded_essentialRelation_of_filtered_lift
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {ω' : Type w}
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω')
    (s k : ℤ) (n : ℕ) {T : C}
    (a : T ⟶ Subobject.underlying.obj
      ((unboundedUnderlyingComplex cm t).fil s k))
    (b : T ⟶ Subobject.underlying.obj
      ((unboundedUnderlyingComplex cm t).fil (s + (n : ℤ)) (k - 1)))
    (hdb : a ≫ ((unboundedUnderlyingComplex cm t).fil s k).arrow ≫
        (unboundedUnderlyingComplex cm t).d k =
      b ≫ ((unboundedUnderlyingComplex cm t).fil
        (s + (n : ℤ)) (k - 1)).arrow)
    (hn : ¬ Subobject.Factors
      ((unboundedUnderlyingComplex cm t).boundarySubobject
        (s + (n : ℤ)) (k - 1) (n : WithTop ℕ))
      (b ≫ (unboundedUnderlyingComplex cm t).filToAssocGraded
        (s + (n : ℤ)) (k - 1))) :
    EssentialDifferentialRelation (ExtensionSpectralSequence cm t)
      (n : ℤ) (s, k)
      (UnboundedExtensionClass cm t s k
        (a ≫ (unboundedUnderlyingComplex cm t).filToAssocGraded s k))
      (UnboundedExtensionClass cm t (s + (n : ℤ)) (k - 1)
        (b ≫ (unboundedUnderlyingComplex cm t).filToAssocGraded
          (s + (n : ℤ)) (k - 1)) :
        T ⟶ ((ExtensionSpectralSequence cm t).ssData
          ((s, k) + (ExtensionSpectralSequence cm t).diffDeg (n : ℤ))).V) := by
  let FC := unboundedUnderlyingComplex cm t
  let j := Subobject.ofLE (FC.fil (s + (n : ℤ)) (k - 1))
    (FC.fil s (k - 1)) (FC.fil_anti_of_le (k - 1) (by omega))
  have hd : a ≫ FC.filDiff s k = b ≫ j := by
    apply (cancel_mono (FC.fil s (k - 1)).arrow).mp
    calc
      (a ≫ FC.filDiff s k) ≫ (FC.fil s (k - 1)).arrow =
          a ≫ (FC.fil s k).arrow ≫ FC.d k := by
            simp only [Category.assoc, FC.filDiff_comp_arrow]
      _ = b ≫ (FC.fil (s + (n : ℤ)) (k - 1)).arrow := hdb
      _ = (b ≫ j) ≫ (FC.fil s (k - 1)).arrow := by
            simp only [Category.assoc, j, Subobject.ofLE_arrow]
  constructor
  · apply unboundedDifferentialRelation_of_lift cm t (n : ℤ)
      (Int.natCast_nonneg n) s k
    · unfold UnboundedExtensionIsLift UnboundedExtensionClass
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rfl
    · unfold UnboundedExtensionIsLift UnboundedExtensionClass
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rfl
    · exact hd
  · intro hfac
    have hfacC := unboundedExtension_boundary_factors_forward cm t
      (s + (n : ℤ)) (k - 1) (n : WithTop ℕ) hfac
    apply hn
    change Subobject.Factors
      ((unboundedComplexSSDataFamily cm t
        (s + (n : ℤ), k - 1)).B (n : WithTop ℕ))
      (b ≫ FC.filToAssocGraded (s + (n : ℤ)) (k - 1))
    let aC : T ⟶ (unboundedComplexSSDataFamily cm t
        (s + (n : ℤ), k - 1)).V := by
      change T ⟶ FC.assocGraded (s + (n : ℤ)) (k - 1)
      exact b ≫ FC.filToAssocGraded (s + (n : ℤ)) (k - 1)
    have hclass : UnboundedExtensionClass cm t
        (s + (n : ℤ)) (k - 1) aC =
        aC ≫ (unboundedSSDataBackward cm t).φ
          (s + (n : ℤ), k - 1) := by
      rfl
    have hcancel : (unboundedSSDataBackward cm t).φ
          (s + (n : ℤ), k - 1) ≫
        (unboundedSSDataForward cm t).φ
          (s + (n : ℤ), k - 1) =
        𝟙 ((unboundedComplexSSDataFamily cm t
          (s + (n : ℤ), k - 1)).V) := by
      change (unboundedExtensionVComplexIso cm t
          (s + (n : ℤ)) (k - 1)).inv ≫
        (unboundedExtensionVComplexIso cm t
          (s + (n : ℤ)) (k - 1)).hom = 𝟙 _
      exact (unboundedExtensionVComplexIso cm t
        (s + (n : ℤ)) (k - 1)).inv_hom_id
    have heq : UnboundedExtensionClass cm t
          (s + (n : ℤ)) (k - 1) aC ≫
        (unboundedSSDataForward cm t).φ
          (s + (n : ℤ), k - 1) = aC := by
      rw [hclass, Category.assoc, hcancel, Category.comp_id]
    change Subobject.Factors
      ((unboundedComplexSSDataFamily cm t
        (s + (n : ℤ), k - 1)).B (n : WithTop ℕ))
      (UnboundedExtensionClass cm t (s + (n : ℤ)) (k - 1) aC ≫
        (unboundedSSDataForward cm t).φ
          (s + (n : ℤ), k - 1)) at hfacC
    rw [heq] at hfacC
    change Subobject.Factors
      ((unboundedComplexSSDataFamily cm t
        (s + (n : ℤ), k - 1)).B (n : WithTop ℕ)) aC
    exact hfacC

/-- 上一条定理的显式目标过滤次数版本；等式参数负责唯一的类型搬运。 -/
theorem unbounded_essentialRelation_of_filtered_lift_at_target
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {ω' : Type w}
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω')
    (s p k : ℤ) (n : ℕ) (hsp : s + (n : ℤ) = p) {T : C}
    (a : T ⟶ Subobject.underlying.obj
      ((unboundedUnderlyingComplex cm t).fil s k))
    (b : T ⟶ Subobject.underlying.obj
      ((unboundedUnderlyingComplex cm t).fil p (k - 1)))
    (hdb : a ≫ ((unboundedUnderlyingComplex cm t).fil s k).arrow ≫
        (unboundedUnderlyingComplex cm t).d k =
      b ≫ ((unboundedUnderlyingComplex cm t).fil p (k - 1)).arrow)
    (hn : ¬ ((unboundedUnderlyingComplex cm t).boundarySubobject
      p (k - 1) (n : WithTop ℕ)).Factors
        (b ≫ (unboundedUnderlyingComplex cm t).filToAssocGraded p (k - 1))) :
    EssentialDifferentialRelation (ExtensionSpectralSequence cm t)
      (n : ℤ) (s, k)
      (UnboundedExtensionClass cm t s k
        (a ≫ (unboundedUnderlyingComplex cm t).filToAssocGraded s k))
      (Eq.mpr (congrArg (fun X : C => T ⟶ X)
        (show ((ExtensionSpectralSequence cm t).ssData
          ((s, k) + (ExtensionSpectralSequence cm t).diffDeg (n : ℤ))).V =
          (unboundedExtensionSSData cm t (p, k - 1)).V by
            rw [← hsp]
            rfl))
        (UnboundedExtensionClass cm t p (k - 1)
          (b ≫ (unboundedUnderlyingComplex cm t).filToAssocGraded p (k - 1)))) := by
  subst p
  exact unbounded_essentialRelation_of_filtered_lift cm t s k n a b hdb hn

/-- 无界扩张谱序列中的本质微分只能出现在非负页。 -/
theorem unbounded_essentialRelation_nonneg
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {ω' : Type w}
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    (cm : ConvergenceMorphism conv₁ conv₂) (t : ω')
    (r : ℤ) (index : ℤ × ℤ) {T : C}
    {x : T ⟶ ((ExtensionSpectralSequence cm t).ssData index).V}
    {y : T ⟶ ((ExtensionSpectralSequence cm t).ssData
      (index + (ExtensionSpectralSequence cm t).diffDeg r)).V}
    (h : EssentialDifferentialRelation (ExtensionSpectralSequence cm t)
      r index x y) :
    0 ≤ r := by
  by_contra hn
  exact (h.d_ne_zero (ExtensionSpectralSequence cm t) r index)
    (ExtensionSpectralSequence_d_neg cm t r (by omega) index)

/-- 无界复形中一个非零有限页边缘，来自过滤次数更高的本质微分。
证明只对给定的有限页数归纳，因此不需要过滤有界。 -/
theorem unbounded_essential_ancestor_of_nonzero_boundary
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {ω' : Type w}
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    (cm : ConvergenceMorphism conv₁ conv₂) (τ : ω') (k : ℤ)
    (m : ℕ) (t p : ℤ) (ht : t + (m : ℤ) = p)
    {T : C} [Projective T]
    (v : T ⟶ (unboundedUnderlyingComplex cm τ).assocGraded p (k - 1))
    (hv : v ≠ 0)
    (hb : ((unboundedUnderlyingComplex cm τ).boundarySubobject
      p (k - 1) (m : WithTop ℕ)).Factors v) :
    ∃ (u : ℤ) (j : ℕ) (huj : u + (j : ℤ) = p)
      (x' : T ⟶ (unboundedUnderlyingComplex cm τ).assocGraded u k),
      t < u ∧ EssentialDifferentialRelation (ExtensionSpectralSequence cm τ)
        (j : ℤ) (u, k)
        (UnboundedExtensionClass cm τ u k x')
        (Eq.mpr (congrArg (fun X : C => T ⟶ X)
          (show ((ExtensionSpectralSequence cm τ).ssData
            ((u, k) + (ExtensionSpectralSequence cm τ).diffDeg (j : ℤ))).V =
            (unboundedExtensionSSData cm τ (p, k - 1)).V by
              rw [← huj]
              rfl))
          (UnboundedExtensionClass cm τ p (k - 1) v)) := by
  let FC := unboundedUnderlyingComplex cm τ
  induction m generalizing t p with
  | zero =>
      cases ht
      have hvzero : v = 0 := by
        simpa only [Int.cast_zero, add_zero, FC] using
          (FC.boundary_zero_apply (t + (0 : ℤ)) k hb)
      exact (hv hvzero).elim
  | succ n ih =>
      cases ht
      obtain ⟨a, b, hdb, hbb⟩ :=
        FC.lift_boundary_at_differential t k (n + 1) hb
      have ht' : (t + 1) + (n : ℤ) = t + ((n + 1 : ℕ) : ℤ) := by omega
      by_cases hbn : (FC.boundarySubobject
          (t + ((n + 1 : ℕ) : ℤ)) (k - 1) (n : WithTop ℕ)).Factors v
      · obtain ⟨u, j, huj, x', htu, hess⟩ :=
          ih (t + 1) (t + ((n + 1 : ℕ) : ℤ)) ht' v hv hbn
        exact ⟨u, j, huj, x', by omega, hess⟩
      · have hnot : ¬ (FC.boundarySubobject
            (t + ((n + 1 : ℕ) : ℤ)) (k - 1) (n : WithTop ℕ)).Factors
            (b ≫ FC.filToAssocGraded
              (t + ((n + 1 : ℕ) : ℤ)) (k - 1)) := by
          rwa [hbb]
        have hess := unbounded_essentialRelation_of_filtered_lift_at_target
          cm τ (t + 1) (t + ((n + 1 : ℕ) : ℤ)) k n ht' a b hdb hnot
        rw [hbb] at hess
        exact ⟨t + 1, n, ht',
          a ≫ FC.filToAssocGraded (t + 1) k, by omega, hess⟩

/-- 范围无 crossing 排除该有限目标区间中的非零边缘。这里只调用上一条
有限页祖先定理，所以无界过滤在区间外的行为无关。 -/
theorem unbounded_no_nonzero_boundary
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {ω' : Type w}
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    (cm : ConvergenceMorphism conv₁ conv₂) (τ : ω')
    (r s k p : ℤ) {T : C} [Projective T]
    {x : T ⟶ ((ExtensionSpectralSequence cm τ).ssData (s, k)).V}
    {y : T ⟶ ((ExtensionSpectralSequence cm τ).ssData
      ((s, k) + (ExtensionSpectralSequence cm τ).diffDeg r)).V}
    (hrel : DifferentialRelation (ExtensionSpectralSequence cm τ)
      r (s, k) x y)
    (hnc : ESSRelationNoCrossingRange r (s, k) hrel p)
    (t q : ℤ) (m : ℕ) (ht : t + (m : ℤ) = q)
    (hst : s ≤ t) (hpq : p ≤ q) (hqr : q ≤ s + r)
    (v : T ⟶ (unboundedUnderlyingComplex cm τ).assocGraded q (k - 1))
    (hb : ((unboundedUnderlyingComplex cm τ).boundarySubobject
      q (k - 1) (m : WithTop ℕ)).Factors v) :
    v = 0 := by
  by_contra hv
  obtain ⟨u, j, huj, x', htu, hess⟩ :=
    unbounded_essential_ancestor_of_nonzero_boundary
      cm τ k m t q ht v hv hb
  unfold ESSRelationNoCrossingRange
    ExtensionDifferentialRelation.NoCrossingRange at hnc
  apply hnc
  refine ⟨u - s, by omega, (j : ℤ), (u, k), _, _, ?_, hess, ?_, ?_⟩
  · change u = s + (u - s)
    omega
  · change p ≤ u + (j : ℤ)
    omega
  · change u + (j : ℤ) ≤ s + r
    omega

/-- 无界扩张谱序列中，在指定范围无 crossing 时，同源同页的目标唯一。
两个目标之差先落入有限 `B_r`，再由上一条有限区间结论消去。 -/
theorem unbounded_target_unique
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {ω' : Type w}
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    (cm : ConvergenceMorphism conv₁ conv₂) (τ : ω')
    (r : ℤ) (hr : 0 ≤ r) (s k p : ℤ) (hp : p ≤ s + r)
    {T : C} [Projective T]
    {x : T ⟶ ((ExtensionSpectralSequence cm τ).ssData (s, k)).V}
    {y₁ y₂ : T ⟶ ((ExtensionSpectralSequence cm τ).ssData
      ((s, k) + (ExtensionSpectralSequence cm τ).diffDeg r)).V}
    (h₁ : DifferentialRelation (ExtensionSpectralSequence cm τ)
      r (s, k) x y₁)
    (h₂ : DifferentialRelation (ExtensionSpectralSequence cm τ)
      r (s, k) x y₂)
    (hnc : ESSRelationNoCrossingRange r (s, k) h₁ p) :
    y₁ = y₂ := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hr
  have hb := DifferentialRelation.targets_sub_factors_boundary
    (ExtensionSpectralSequence cm τ) (n : ℤ) (s, k) h₁ h₂
  change ((unboundedExtensionSSData cm τ
    (s + (n : ℤ), k - 1)).B (n : WithTop ℕ)).Factors (y₁ - y₂) at hb
  have hbC := unboundedExtension_boundary_factors_forward cm τ
    (s + (n : ℤ)) (k - 1) (n : WithTop ℕ) hb
  have hz : (y₁ - y₂) ≫
      (unboundedExtensionVComplexIso cm τ
        (s + (n : ℤ)) (k - 1)).hom = 0 :=
    unbounded_no_nonzero_boundary cm τ (n : ℤ) s k p h₁ hnc
      s (s + (n : ℤ)) n (by omega) (by omega) hp (by omega) _ hbC
  have hsub : y₁ - y₂ = 0 := by
    apply (cancel_mono (unboundedExtensionVComplexIso cm τ
      (s + (n : ℤ)) (k - 1)).hom).mp
    calc
      (y₁ - y₂) ≫ (unboundedExtensionVComplexIso cm τ
          (s + (n : ℤ)) (k - 1)).hom = 0 := hz
      _ = 0 ≫ (unboundedExtensionVComplexIso cm τ
          (s + (n : ℤ)) (k - 1)).hom := zero_comp.symm
  exact sub_eq_zero.mp hsub

/-- 在有限整数区间中寻找最后一个仍可分解的过滤层。与有界版本不同，
这里只在给定右端点以前搜索，因此不要求整个过滤有上界。 -/
theorem FilteredComplex.factor_max_on_finite_interval
    (FC : FilteredComplex C) (p q k : ℤ) (hpq : p ≤ q)
    {T : C} (v : T ⟶ FC.A k)
    (hp : (FC.fil p k).Factors v) :
    (FC.fil q k).Factors v ∨
      ∃ j : ℤ, p ≤ j ∧ j < q ∧
        (FC.fil j k).Factors v ∧ ¬ (FC.fil (j + 1) k).Factors v := by
  classical
  by_cases hpq' : p = q
  · left
    simpa only [hpq'] using hp
  · have hp_lt_q : p < q := lt_of_le_of_ne hpq hpq'
    by_cases hp1 : (FC.fil (p + 1) k).Factors v
    · rcases FC.factor_max_on_finite_interval (p + 1) q k (by omega) v hp1 with
        hq | ⟨j, hpj, hjq, hj, hjmax⟩
      · exact Or.inl hq
      · exact Or.inr ⟨j, by omega, hjq, hj, hjmax⟩
    · exact Or.inr ⟨p, le_rfl, hp_lt_q, hp, hp1⟩
termination_by (q - p).toNat
decreasing_by omega

/-- 更高过滤源的微分一旦进入指定范围下界，就必须进入原关系的完整
目标过滤层。最大层只在有限区间内选取，故该论证适用于无界过滤。 -/
theorem unbounded_higher_source_image_deeper
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {ω' : Type w}
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    (cm : ConvergenceMorphism conv₁ conv₂) (τ : ω')
    (r s k p : ℤ) (hpr : p ≤ s + r) {T : C} [Projective T]
    {x : T ⟶ ((ExtensionSpectralSequence cm τ).ssData (s, k)).V}
    {y : T ⟶ ((ExtensionSpectralSequence cm τ).ssData
      ((s, k) + (ExtensionSpectralSequence cm τ).diffDeg r)).V}
    (hrel : DifferentialRelation (ExtensionSpectralSequence cm τ)
      r (s, k) x y)
    (hnc : ESSRelationNoCrossingRange r (s, k) hrel p)
    (t : ℤ) (hst : s < t)
    (a : T ⟶ Subobject.underlying.obj
      ((unboundedUnderlyingComplex cm τ).fil t k))
    (hp : ((unboundedUnderlyingComplex cm τ).fil p (k - 1)).Factors
      (a ≫ ((unboundedUnderlyingComplex cm τ).fil t k).arrow ≫
        (unboundedUnderlyingComplex cm τ).d k)) :
    ((unboundedUnderlyingComplex cm τ).fil (s + r) (k - 1)).Factors
      (a ≫ ((unboundedUnderlyingComplex cm τ).fil t k).arrow ≫
        (unboundedUnderlyingComplex cm τ).d k) := by
  classical
  let FC := unboundedUnderlyingComplex cm τ
  let v := a ≫ (FC.fil t k).arrow ≫ FC.d k
  have hv_t : (FC.fil t (k - 1)).Factors v := by
    change (FC.fil t (k - 1)).Factors
      (a ≫ (FC.fil t k).arrow ≫ FC.d k)
    rw [← FC.filDiff_comp_arrow]
    simpa only [Category.assoc] using
      (Subobject.factors_comp_arrow (a ≫ FC.filDiff t k))
  rcases FC.factor_max_on_finite_interval p (s + r) (k - 1)
      hpr v hp with htarget | ⟨q, hpq, hqr, hqfac, hqmax⟩
  · exact htarget
  have htq : t ≤ q := by
    by_contra hn
    have hle : FC.fil t (k - 1) ≤ FC.fil (q + 1) (k - 1) :=
      FC.fil_anti_of_le (k - 1) (by omega)
    exact hqmax (Subobject.factors_of_le v hle hv_t)
  let b := (FC.fil q (k - 1)).factorThru v hqfac
  have hdb : a ≫ (FC.fil t k).arrow ≫ FC.d k =
      b ≫ (FC.fil q (k - 1)).arrow := by
    exact ((FC.fil q (k - 1)).factorThru_arrow v hqfac).symm
  let m : ℕ := (q - t).toNat
  have htm : t + (m : ℤ) = q := by
    dsimp only [m]
    omega
  have hyne : b ≫ FC.filToAssocGraded q (k - 1) ≠ 0 :=
    FC.assocGraded_ne_zero_of_maximal q (k - 1) b
      (by simpa [b, v] using hqmax)
  by_cases hb : (FC.boundarySubobject q (k - 1) (m : WithTop ℕ)).Factors
      (b ≫ FC.filToAssocGraded q (k - 1))
  · exfalso
    exact hyne (unbounded_no_nonzero_boundary cm τ r s k p hrel hnc
      t q m htm (le_of_lt hst) hpq (le_of_lt hqr)
      (b ≫ FC.filToAssocGraded q (k - 1)) hb)
  · have hess := unbounded_essentialRelation_of_filtered_lift_at_target
      cm τ t q k m htm a b hdb hb
    unfold ESSRelationNoCrossingRange
      ExtensionDifferentialRelation.NoCrossingRange at hnc
    exfalso
    apply hnc
    refine ⟨t - s, by omega, (m : ℤ), (t, k), _, _, ?_, hess, ?_, ?_⟩
    · change t = s + (t - s)
      omega
    · change p ≤ t + (m : ℤ)
      omega
    · change t + (m : ℤ) ≤ s + r
      omega

/-- 范围无 crossing 的代表元检测：给定一个已检测目标的参照提升，任何
与它同类且差值微分进入范围下界的提升，都检测同一个目标。 -/
theorem unbounded_uniform_detection_from_reference
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {ω' : Type w}
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    (cm : ConvergenceMorphism conv₁ conv₂) (τ : ω')
    (r : ℤ) (hr : 0 ≤ r) (s k p : ℤ) (hpr : p ≤ s + r)
    {T : C} [Projective T]
    {x : T ⟶ ((ExtensionSpectralSequence cm τ).ssData (s, k)).V}
    {y : T ⟶ ((ExtensionSpectralSequence cm τ).ssData
      ((s, k) + (ExtensionSpectralSequence cm τ).diffDeg r)).V}
    (hrel : DifferentialRelation (ExtensionSpectralSequence cm τ)
      r (s, k) x y)
    (hnc : ESSRelationNoCrossingRange r (s, k) hrel p)
    (x₀ xl : T ⟶ Subobject.underlying.obj
      ((unboundedUnderlyingComplex cm τ).fil s k))
    (y₀ : T ⟶ Subobject.underlying.obj
      ((unboundedUnderlyingComplex cm τ).fil (s + r) (k - 1)))
    (hx₀ : UnboundedExtensionIsLift cm τ s k x₀ x)
    (hx : UnboundedExtensionIsLift cm τ s k xl x)
    (hd₀ : x₀ ≫ (unboundedUnderlyingComplex cm τ).filDiff s k =
      y₀ ≫ Subobject.ofLE
        ((unboundedUnderlyingComplex cm τ).fil (s + r) (k - 1))
        ((unboundedUnderlyingComplex cm τ).fil s (k - 1))
        ((unboundedUnderlyingComplex cm τ).fil_anti_of_le (k - 1) (by omega)))
    (v : T ⟶ Subobject.underlying.obj
      ((unboundedUnderlyingComplex cm τ).fil (s + 1) k))
    (hv : v ≫ Subobject.ofLE
      ((unboundedUnderlyingComplex cm τ).fil (s + 1) k)
      ((unboundedUnderlyingComplex cm τ).fil s k)
      ((unboundedUnderlyingComplex cm τ).fil_anti s k) = xl - x₀)
    (hp : ((unboundedUnderlyingComplex cm τ).fil p (k - 1)).Factors
      (v ≫ ((unboundedUnderlyingComplex cm τ).fil (s + 1) k).arrow ≫
        (unboundedUnderlyingComplex cm τ).d k)) :
    ∃ yl : T ⟶ Subobject.underlying.obj
        ((unboundedUnderlyingComplex cm τ).fil (s + r) (k - 1)),
      xl ≫ (unboundedUnderlyingComplex cm τ).filDiff s k =
        yl ≫ Subobject.ofLE
          ((unboundedUnderlyingComplex cm τ).fil (s + r) (k - 1))
          ((unboundedUnderlyingComplex cm τ).fil s (k - 1))
          ((unboundedUnderlyingComplex cm τ).fil_anti_of_le (k - 1) (by omega)) ∧
      UnboundedExtensionIsLift cm τ (s + r) (k - 1) yl y := by
  classical
  let FC := unboundedUnderlyingComplex cm τ
  have htarget := unbounded_higher_source_image_deeper
    cm τ r s k p hpr hrel hnc (s + 1) (by omega) v hp
  let c := (FC.fil (s + r) (k - 1)).factorThru
    (v ≫ (FC.fil (s + 1) k).arrow ≫ FC.d k) htarget
  have hdiff_sub : (xl - x₀) ≫ (FC.fil s k).arrow ≫ FC.d k =
      c ≫ (FC.fil (s + r) (k - 1)).arrow := by
    calc
      (xl - x₀) ≫ (FC.fil s k).arrow ≫ FC.d k =
          (v ≫ Subobject.ofLE (FC.fil (s + 1) k) (FC.fil s k)
            (FC.fil_anti s k)) ≫ (FC.fil s k).arrow ≫ FC.d k := by rw [hv]
      _ = v ≫ (FC.fil (s + 1) k).arrow ≫ FC.d k := by
        have hinc : Subobject.ofLE (FC.fil (s + 1) k) (FC.fil s k)
            (FC.fil_anti s k) ≫ (FC.fil s k).arrow =
            (FC.fil (s + 1) k).arrow := Subobject.ofLE_arrow _
        simpa only [Category.assoc] using
          congrArg (fun f => v ≫ f ≫ FC.d k) hinc
      _ = c ≫ (FC.fil (s + r) (k - 1)).arrow := by
        exact ((FC.fil (s + r) (k - 1)).factorThru_arrow _ htarget).symm
  have hdiff₀ : x₀ ≫ (FC.fil s k).arrow ≫ FC.d k =
      y₀ ≫ (FC.fil (s + r) (k - 1)).arrow := by
    rw [← FC.filDiff_comp_arrow]
    rw [← Category.assoc, hd₀]
    simp only [FC, Category.assoc, Subobject.ofLE_arrow]
  let yl := y₀ + c
  have hdiff : xl ≫ FC.filDiff s k =
      yl ≫ Subobject.ofLE (FC.fil (s + r) (k - 1))
        (FC.fil s (k - 1)) (FC.fil_anti_of_le (k - 1) (by omega)) := by
    apply (cancel_mono (FC.fil s (k - 1)).arrow).mp
    simp only [Category.assoc, FC.filDiff_comp_arrow, Subobject.ofLE_arrow]
    change xl ≫ (FC.fil s k).arrow ≫ FC.d k =
      (y₀ + c) ≫ (FC.fil (s + r) (k - 1)).arrow
    rw [Preadditive.add_comp, ← hdiff₀, ← hdiff_sub]
    simp only [Preadditive.sub_comp]
    abel
  let y' := UnboundedExtensionClass cm τ (s + r) (k - 1)
    (yl ≫ FC.filToAssocGraded (s + r) (k - 1))
  have hy' : UnboundedExtensionIsLift cm τ (s + r) (k - 1) yl y' := by
    dsimp only [y']
    unfold UnboundedExtensionIsLift UnboundedExtensionClass
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl
  have hrel' : DifferentialRelation (ExtensionSpectralSequence cm τ)
      r (s, k) x y' :=
    unboundedDifferentialRelation_of_lift cm τ r hr s k hx hy' hdiff
  have heq := unbounded_target_unique cm τ r hr s k p hpr hrel hrel' hnc
  refine ⟨yl, hdiff, ?_⟩
  rw [heq]
  exact hy'

/-- 第零页的目标过滤次数等于源过滤次数，因此其目标范围自动无 crossing。 -/
theorem unbounded_zero_page_automatic
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {ω' : Type w}
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    (cm : ConvergenceMorphism conv₁ conv₂) (τ : ω')
    (s k : ℤ) {T : C} [Projective T]
    {x : T ⟶ ((ExtensionSpectralSequence cm τ).ssData (s, k)).V}
    {y : T ⟶ ((ExtensionSpectralSequence cm τ).ssData
      ((s, k) + (ExtensionSpectralSequence cm τ).diffDeg 0)).V}
    (hrel : DifferentialRelation (ExtensionSpectralSequence cm τ)
      0 (s, k) x y) :
    ESSRelationNoCrossingRange 0 (s, k) hrel s := by
  intro hc
  rcases hc with ⟨a, ha, m, index, x', y', hs, he, _hp, hupper⟩
  have hm := unbounded_essentialRelation_nonneg cm τ m index he
  change index.1 = s + a at hs
  change (index + (ExtensionSpectralSequence cm τ).diffDeg m).1 ≤ s + 0 at hupper
  rw [ExtensionSpectralSequence_diffDeg] at hupper
  simp only [Prod.fst_add, add_zero] at hupper
  omega

/-- 无界 ESS 中一条无 crossing 关系对任意源代表元都给出统一目标代表元。 -/
theorem unbounded_uniform_detection
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {ω' : Type w}
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    (cm : ConvergenceMorphism conv₁ conv₂) (τ : ω')
    (r : ℤ) (hr : 0 ≤ r) (s k : ℤ) {T : C} [Projective T]
    {x : T ⟶ ((ExtensionSpectralSequence cm τ).ssData (s, k)).V}
    {y : T ⟶ ((ExtensionSpectralSequence cm τ).ssData
      ((s, k) + (ExtensionSpectralSequence cm τ).diffDeg r)).V}
    (hrel : DifferentialRelation (ExtensionSpectralSequence cm τ)
      r (s, k) x y)
    (hnc : ESSRelationNoCrossing r (s, k) hrel)
    (xl : T ⟶ Subobject.underlying.obj
      ((unboundedUnderlyingComplex cm τ).fil s k))
    (hx : UnboundedExtensionIsLift cm τ s k xl x) :
    ∃ yl : T ⟶ Subobject.underlying.obj
        ((unboundedUnderlyingComplex cm τ).fil (s + r) (k - 1)),
      xl ≫ (unboundedUnderlyingComplex cm τ).filDiff s k =
        yl ≫ Subobject.ofLE
          ((unboundedUnderlyingComplex cm τ).fil (s + r) (k - 1))
          ((unboundedUnderlyingComplex cm τ).fil s (k - 1))
          ((unboundedUnderlyingComplex cm τ).fil_anti_of_le (k - 1) (by omega)) ∧
      UnboundedExtensionIsLift cm τ (s + r) (k - 1) yl y := by
  classical
  let FC := unboundedUnderlyingComplex cm τ
  obtain ⟨x₀, y₀, hx₀, _hy₀, hd₀⟩ :=
    unbounded_lift_of_differentialRelation cm τ r hr s k hrel
  have hxc := hx
  have hx₀c := hx₀
  unfold UnboundedExtensionIsLift at hxc hx₀c
  obtain ⟨v, hv⟩ := FC.isLift_sub_lift s k hxc hx₀c
  rcases eq_or_lt_of_le hr with hzero | hpos
  · subst r
    have hp : (FC.fil s (k - 1)).Factors
        (v ≫ (FC.fil (s + 1) k).arrow ≫ FC.d k) := by
      rw [← FC.filDiff_comp_arrow]
      exact Subobject.factors_of_le _ (FC.fil_anti s (k - 1))
        (by simpa only [Category.assoc] using
          (Subobject.factors_comp_arrow (v ≫ FC.filDiff (s + 1) k)))
    exact unbounded_uniform_detection_from_reference cm τ 0 (by omega)
      s k s (by omega) hrel
      (unbounded_zero_page_automatic cm τ s k hrel)
      x₀ xl y₀ hx₀ hx hd₀ v hv hp
  · have hp : (FC.fil (s + 1) (k - 1)).Factors
        (v ≫ (FC.fil (s + 1) k).arrow ≫ FC.d k) := by
      rw [← FC.filDiff_comp_arrow]
      simpa only [Category.assoc] using
        (Subobject.factors_comp_arrow (v ≫ FC.filDiff (s + 1) k))
    exact unbounded_uniform_detection_from_reference cm τ r hr
      s k (s + 1) (by omega) hrel hnc
      x₀ xl y₀ hx₀ hx hd₀ v hv hp

/-- 零目标关系无 crossing 时，任意源提升的微分严格落入目标下一过滤层。 -/
theorem unbounded_zero_uniform_deeper
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {ω' : Type w}
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    (cm : ConvergenceMorphism conv₁ conv₂) (τ : ω')
    (r : ℤ) (hr : 0 ≤ r) (s k : ℤ) {T : C} [Projective T]
    {x : T ⟶ ((ExtensionSpectralSequence cm τ).ssData (s, k)).V}
    (hrel : DifferentialRelation (ExtensionSpectralSequence cm τ)
      r (s, k) x 0)
    (hnc : ESSRelationNoCrossing r (s, k) hrel)
    (xl : T ⟶ Subobject.underlying.obj
      ((unboundedUnderlyingComplex cm τ).fil s k))
    (hx : UnboundedExtensionIsLift cm τ s k xl x) :
    ∃ yd : T ⟶ Subobject.underlying.obj
        ((unboundedUnderlyingComplex cm τ).fil (s + r + 1) (k - 1)),
      xl ≫ (unboundedUnderlyingComplex cm τ).filDiff s k =
        yd ≫ Subobject.ofLE
          ((unboundedUnderlyingComplex cm τ).fil (s + r + 1) (k - 1))
          ((unboundedUnderlyingComplex cm τ).fil s (k - 1))
          ((unboundedUnderlyingComplex cm τ).fil_anti_of_le (k - 1) (by omega)) := by
  let FC := unboundedUnderlyingComplex cm τ
  obtain ⟨yl, hd, hy⟩ :=
    unbounded_uniform_detection cm τ r hr s k hrel hnc xl hx
  unfold UnboundedExtensionIsLift at hy
  have hyzero : FC.IsLift (s + r) (k - 1) yl 0 := by
    change (unboundedUnderlyingComplex cm τ).IsLift
      (s + r) (k - 1) yl 0
    change (unboundedUnderlyingComplex cm τ).IsLift
      (s + r) (k - 1) yl
        (0 ≫ (unboundedExtensionVComplexIso cm τ
          (s + r) (k - 1)).hom) at hy
    rw [zero_comp] at hy
    exact hy
  obtain ⟨yd, hdeeper⟩ := FC.lift_zero_deeper (s + r) (k - 1) yl hyzero
  refine ⟨yd, ?_⟩
  apply (cancel_mono (FC.fil s (k - 1)).arrow).mp
  rw [hd, ← hdeeper]
  simp only [FC, Category.assoc, Subobject.ofLE_arrow]

/-! ## 无界版第 2.12 条 -/

/-- 若方块左出的两条关系至少一条无 crossing，则可在未截断复形中选择
同一个源提升，同时实现两条边的指定目标。四个 ESS 在这里仍彼此不同；
共享只发生在原始谱序列的公共 `E∞` 顶点。 -/
theorem unbounded_comm_common_source_lift
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {ω' : Type w}
    (sq : ConvergingSSSquare (C := C) (ω := ω) (ω' := ω'))
    (n m s : ℤ) (τ : ω') {T : C} [Projective T]
    (hn : 0 ≤ n) (hm : 0 ≤ m)
    (x : T ⟶ (sq.V₁.E.ssData
      (sq.V₁.conv.reindexEquiv.symm (s, τ))).eInfty)
    (y : T ⟶ (sq.V₂.E.ssData
      (sq.V₂.conv.reindexEquiv.symm (s + n, τ))).eInfty)
    (z : T ⟶ (sq.V₃.E.ssData
      (sq.V₃.conv.reindexEquiv.symm (s + m, τ))).eInfty)
    (hf : DifferentialRelation (ExtensionSpectralSequence sq.f τ)
      n (s, 1) x y)
    (hp : DifferentialRelation (ExtensionSpectralSequence sq.p τ)
      m (s, 1) x z)
    (hnc : ESSRelationNoCrossing n (s, 1) hf ∨
      ESSRelationNoCrossing m (s, 1) hp) :
    ∃ (xl : T ⟶ Subobject.underlying.obj
          ((unboundedUnderlyingComplex sq.f τ).fil s 1))
      (yl : T ⟶ Subobject.underlying.obj
          ((unboundedUnderlyingComplex sq.f τ).fil (s + n) 0))
      (zl : T ⟶ Subobject.underlying.obj
          ((unboundedUnderlyingComplex sq.p τ).fil (s + m) 0)),
      UnboundedExtensionIsLift sq.f τ s 1 xl x ∧
      UnboundedExtensionIsLift sq.f τ (s + n) 0 yl y ∧
      UnboundedExtensionIsLift sq.p τ (s + m) 0 zl z ∧
      xl ≫ (unboundedUnderlyingComplex sq.f τ).filDiff s 1 =
        yl ≫ Subobject.ofLE
          ((unboundedUnderlyingComplex sq.f τ).fil (s + n) 0)
          ((unboundedUnderlyingComplex sq.f τ).fil s 0)
          ((unboundedUnderlyingComplex sq.f τ).fil_anti_of_le 0 (by omega)) ∧
      xl ≫ (unboundedUnderlyingComplex sq.p τ).filDiff s 1 =
        zl ≫ Subobject.ofLE
          ((unboundedUnderlyingComplex sq.p τ).fil (s + m) 0)
          ((unboundedUnderlyingComplex sq.p τ).fil s 0)
          ((unboundedUnderlyingComplex sq.p τ).fil_anti_of_le 0 (by omega)) := by
  rcases hnc with hfnc | hpnc
  · obtain ⟨xl, zl, hx, hz, hdz⟩ :=
      unbounded_lift_of_differentialRelation sq.p τ m hm s 1 hp
    change T ⟶ Subobject.underlying.obj
      ((unboundedUnderlyingComplex sq.f τ).fil s 1) at xl
    have hx_f : UnboundedExtensionIsLift sq.f τ s 1 xl x := by
      simpa only using
        (unboundedExtensionIsLift_source_independent
          sq.p sq.f τ s xl x hx)
    obtain ⟨yl, hdy, hy⟩ :=
      unbounded_uniform_detection sq.f τ n hn s 1 hf hfnc xl hx_f
    exact ⟨xl, yl, zl, hx_f, hy, hz, hdy, hdz⟩
  · obtain ⟨xl, yl, hx, hy, hdy⟩ :=
      unbounded_lift_of_differentialRelation sq.f τ n hn s 1 hf
    have hx_p : UnboundedExtensionIsLift sq.p τ s 1 xl x := by
      simpa only using
        (unboundedExtensionIsLift_source_independent
          sq.f sq.p τ s xl x hx)
    obtain ⟨zl, hdz, hz⟩ :=
      unbounded_uniform_detection sq.p τ m hm s 1 hp hpnc xl hx_p
    exact ⟨xl, yl, zl, hx, hy, hz, hdy, hdz⟩

/-- 公共源提升沿交换方块的两条复合在右下环境对象中相等。 -/
theorem unbounded_comm_lift_square_ambient
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {ω' : Type w}
    (sq : ConvergingSSSquare (C := C) (ω := ω) (ω' := ω'))
    (n m s : ℤ) (τ : ω') {T : C}
    (hn : 0 ≤ n) (hm : 0 ≤ m)
    (xl : T ⟶ Subobject.underlying.obj
      ((unboundedUnderlyingComplex sq.f τ).fil s 1))
    (yl : T ⟶ Subobject.underlying.obj
      ((unboundedUnderlyingComplex sq.f τ).fil (s + n) 0))
    (zl : T ⟶ Subobject.underlying.obj
      ((unboundedUnderlyingComplex sq.p τ).fil (s + m) 0))
    (hdy : xl ≫ (unboundedUnderlyingComplex sq.f τ).filDiff s 1 =
      yl ≫ Subobject.ofLE
        ((unboundedUnderlyingComplex sq.f τ).fil (s + n) 0)
        ((unboundedUnderlyingComplex sq.f τ).fil s 0)
        ((unboundedUnderlyingComplex sq.f τ).fil_anti_of_le 0 (by omega)))
    (hdz : xl ≫ (unboundedUnderlyingComplex sq.p τ).filDiff s 1 =
      zl ≫ Subobject.ofLE
        ((unboundedUnderlyingComplex sq.p τ).fil (s + m) 0)
        ((unboundedUnderlyingComplex sq.p τ).fil s 0)
        ((unboundedUnderlyingComplex sq.p τ).fil_anti_of_le 0 (by omega))) :
    yl ≫ ((unboundedUnderlyingComplex sq.f τ).fil (s + n) 0).arrow ≫
        sq.q.aMap τ =
      zl ≫ ((unboundedUnderlyingComplex sq.p τ).fil (s + m) 0).arrow ≫
        sq.g.aMap τ := by
  have hf := unbounded_lift_ambient_map sq.f τ
    s (s + n) (by omega) xl yl hdy
  have hp := unbounded_lift_ambient_map sq.p τ
    s (s + m) (by omega) xl zl hdz
  change xl ≫ (sq.V₁.F.F s τ).arrow ≫ sq.f.aMap τ =
      yl ≫ (sq.V₂.F.F (s + n) τ).arrow at hf
  change xl ≫ (sq.V₁.F.F s τ).arrow ≫ sq.p.aMap τ =
      zl ≫ (sq.V₃.F.F (s + m) τ).arrow at hp
  change yl ≫ (sq.V₂.F.F (s + n) τ).arrow ≫ sq.q.aMap τ =
      zl ≫ (sq.V₃.F.F (s + m) τ).arrow ≫ sq.g.aMap τ
  calc
    yl ≫ (sq.V₂.F.F (s + n) τ).arrow ≫ sq.q.aMap τ =
        xl ≫ (sq.V₁.F.F s τ).arrow ≫ sq.f.aMap τ ≫ sq.q.aMap τ := by
      simpa only [Category.assoc] using
        congrArg (fun u : T ⟶ sq.V₂.A τ => u ≫ sq.q.aMap τ) hf.symm
    _ = xl ≫ (sq.V₁.F.F s τ).arrow ≫ sq.p.aMap τ ≫ sq.g.aMap τ := by
      simpa only [Category.assoc] using
        congrArg (fun u : sq.V₁.A τ ⟶ sq.V₄.A τ =>
          (xl ≫ (sq.V₁.F.F s τ).arrow) ≫ u) (sq.aMap_comm τ)
    _ = zl ≫ (sq.V₃.F.F (s + m) τ).arrow ≫ sq.g.aMap τ := by
      simpa only [Category.assoc] using
        congrArg (fun u : T ⟶ sq.V₃.A τ => u ≫ sq.g.aMap τ) hp

/-- 第 2.12 条结论中，`q` 边的目标页环境正是右下原始谱序列在
过滤次数 `s+m+l` 处的 `E∞` 对象。 -/
theorem unbounded_comm_target_eq
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {ω' : Type w}
    (sq : ConvergingSSSquare (C := C) (ω := ω) (ω' := ω'))
    (n m l s : ℤ) (τ : ω') :
    ((ExtensionSpectralSequence sq.q τ).ssData
      ((s + n, 1) + (ExtensionSpectralSequence sq.q τ).diffDeg
        (m + l - n))).V =
      (sq.V₄.E.ssData
        (sq.V₄.conv.reindexEquiv.symm (s + m + l, τ))).eInfty := by
  have hi : ((s + n, 1) + (ExtensionSpectralSequence sq.q τ).diffDeg
      (m + l - n) : ℤ × ℤ) = (s + m + l, 0) := by
    rw [ExtensionSpectralSequence_diffDeg]
    apply Prod.ext
    · simp only [Prod.fst_add]
      ring
    · rfl
  rw [hi]
  rfl

/-- **无界版定理 2.12**：扩张谱序列微分沿收敛谱序列的交换方块传播。
所有元素直接位于四个原始谱序列的 `E∞` 对象中；四条边对应四个不同的
无界扩张谱序列。证明只使用有限页的 `Z/B` 层和有限过滤区间，因而不要求
过滤有上界。 -/
theorem unboundedEssCommutativity
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {ω' : Type w}
    (sq : ConvergingSSSquare (C := C) (ω := ω) (ω' := ω'))
    (n m l : ℤ) (s : ℤ) (τ : ω')
    (hn : 0 ≤ n) (hm : 0 ≤ m) (hl : 0 ≤ l)
    {T : C} [Projective T]
    (x : T ⟶ (sq.V₁.E.ssData
      (sq.V₁.conv.reindexEquiv.symm (s, τ))).eInfty)
    (y : T ⟶ (sq.V₂.E.ssData
      (sq.V₂.conv.reindexEquiv.symm (s + n, τ))).eInfty)
    (z : T ⟶ (sq.V₃.E.ssData
      (sq.V₃.conv.reindexEquiv.symm (s + m, τ))).eInfty)
    (w : T ⟶ (sq.V₄.E.ssData
      (sq.V₄.conv.reindexEquiv.symm (s + m + l, τ))).eInfty)
    (hf : DifferentialRelation (ExtensionSpectralSequence sq.f τ)
      n (s, 1) x y)
    (hp : DifferentialRelation (ExtensionSpectralSequence sq.p τ)
      m (s, 1) x z)
    (hf_or_p_nc : ESSRelationNoCrossing n (s, 1) hf ∨
      ESSRelationNoCrossing m (s, 1) hp)
    (hg : DifferentialRelation (ExtensionSpectralSequence sq.g τ)
      l (s + m, 1) z w)
    (kval : ℤ) (hk_pos : 0 < kval) (hk_bound : kval ≤ m + l - n)
    (hg_nc : ESSRelationNoCrossingRange l (s + m, 1) hg
      (s + n + kval))
    (hq_zero : DifferentialRelation (ExtensionSpectralSequence sq.q τ)
      (kval - 1) (s + n, 1) y 0)
    (hq_nc : ESSRelationNoCrossing (kval - 1) (s + n, 1) hq_zero) :
    DifferentialRelation (ExtensionSpectralSequence sq.q τ)
      (m + l - n) (s + n, 1) y
      (Eq.mpr (congrArg (fun X : C => T ⟶ X)
        (unbounded_comm_target_eq sq n m l s τ)) w) := by
  classical
  obtain ⟨xl, yl, zl, hx, hy, hz, hdy, hdz⟩ :=
    unbounded_comm_common_source_lift sq n m s τ hn hm x y z
      hf hp hf_or_p_nc
  have hsquare := unbounded_comm_lift_square_ambient
    sq n m s τ hn hm xl yl zl hdy hdz
  have hyq : UnboundedExtensionIsLift sq.q τ (s + n) 1 yl y :=
    unboundedExtensionIsLift_target_source sq.f sq.q τ (s + n) yl y hy
  obtain ⟨qdeep, hqdeep⟩ := unbounded_zero_uniform_deeper
    sq.q τ (kval - 1) (by omega) (s + n) 1
      hq_zero hq_nc yl hyq
  have hqambient := unbounded_lift_ambient_map sq.q τ
    (s + n) (s + n + (kval - 1) + 1) (by omega) yl qdeep hqdeep
  change yl ≫ (sq.V₂.F.F (s + n) τ).arrow ≫ sq.q.aMap τ =
    qdeep ≫ (sq.V₄.F.F (s + n + (kval - 1) + 1) τ).arrow at hqambient
  change yl ≫ (sq.V₂.F.F (s + n) τ).arrow ≫ sq.q.aMap τ =
    zl ≫ (sq.V₃.F.F (s + m) τ).arrow ≫ sq.g.aMap τ at hsquare
  have hgRange : (sq.V₄.F.F (s + n + kval) τ).Factors
      (zl ≫ (sq.V₃.F.F (s + m) τ).arrow ≫ sq.g.aMap τ) := by
    have hraw : zl ≫ (sq.V₃.F.F (s + m) τ).arrow ≫ sq.g.aMap τ =
        qdeep ≫ (sq.V₄.F.F (s + n + (kval - 1) + 1) τ).arrow :=
      hsquare.symm.trans hqambient
    rw [hraw]
    have hle : sq.V₄.F.F (s + n + (kval - 1) + 1) τ ≤
        sq.V₄.F.F (s + n + kval) τ := by
      exact sq.V₄.F.mono_of_le (by omega) τ
    exact Subobject.factors_of_le _ hle
      (Subobject.factors_comp_arrow qdeep)
  let FCg := unboundedUnderlyingComplex sq.g τ
  let zl_g : T ⟶ Subobject.underlying.obj (FCg.fil (s + m) 1) := zl
  have hz_g : UnboundedExtensionIsLift sq.g τ (s + m) 1 zl_g z :=
    unboundedExtensionIsLift_target_source sq.p sq.g τ (s + m) zl z hz
  obtain ⟨z₀, w₀, hz₀, hw₀, hdg₀⟩ :=
    unbounded_lift_of_differentialRelation sq.g τ l hl (s + m) 1 hg
  have hz_gc := hz_g
  have hz₀c := hz₀
  unfold UnboundedExtensionIsLift at hz_gc hz₀c
  obtain ⟨v, hv⟩ := FCg.isLift_sub_lift (s + m) 1 hz_gc hz₀c
  have hg₀ambient := unbounded_lift_ambient_map sq.g τ
    (s + m) (s + m + l) (by omega) z₀ w₀ hdg₀
  change z₀ ≫ (sq.V₃.F.F (s + m) τ).arrow ≫ sq.g.aMap τ =
    w₀ ≫ (sq.V₄.F.F (s + m + l) τ).arrow at hg₀ambient
  have hg₀Range : (sq.V₄.F.F (s + n + kval) τ).Factors
      (z₀ ≫ (sq.V₃.F.F (s + m) τ).arrow ≫ sq.g.aMap τ) := by
    rw [hg₀ambient]
    have hle : sq.V₄.F.F (s + m + l) τ ≤
        sq.V₄.F.F (s + n + kval) τ :=
      sq.V₄.F.mono_of_le (by omega) τ
    exact Subobject.factors_of_le _ hle
      (Subobject.factors_comp_arrow w₀)
  have hgDiffRange : (sq.V₄.F.F (s + n + kval) τ).Factors
      ((zl_g - z₀) ≫ (sq.V₃.F.F (s + m) τ).arrow ≫ sq.g.aMap τ) := by
    have hgRange_g : (sq.V₄.F.F (s + n + kval) τ).Factors
        (zl_g ≫ (sq.V₃.F.F (s + m) τ).arrow ≫ sq.g.aMap τ) := by
      change (sq.V₄.F.F (s + n + kval) τ).Factors
        (zl ≫ (sq.V₃.F.F (s + m) τ).arrow ≫ sq.g.aMap τ)
      exact hgRange
    rcases (Subobject.factors_iff _ _).1 hgRange_g with ⟨az, haz⟩
    rcases (Subobject.factors_iff _ _).1 hg₀Range with ⟨a₀, ha₀⟩
    refine (Subobject.factors_iff _ _).2 ⟨az - a₀, ?_⟩
    rw [Preadditive.sub_comp, haz, ha₀, ← Preadditive.sub_comp]
  have hgVRange : (FCg.fil (s + n + kval) 0).Factors
      (v ≫ (FCg.fil (s + m + 1) 1).arrow ≫ FCg.d 1) := by
    have hvambient : v ≫ (sq.V₃.F.F (s + m + 1) τ).arrow ≫ sq.g.aMap τ =
        (zl_g - z₀) ≫ (sq.V₃.F.F (s + m) τ).arrow ≫ sq.g.aMap τ := by
      have hinc : Subobject.ofLE (FCg.fil (s + m + 1) 1)
          (FCg.fil (s + m) 1) (FCg.fil_anti (s + m) 1) ≫
          (sq.V₃.F.F (s + m) τ).arrow =
          (sq.V₃.F.F (s + m + 1) τ).arrow := Subobject.ofLE_arrow _
      calc
        v ≫ (sq.V₃.F.F (s + m + 1) τ).arrow ≫ sq.g.aMap τ =
            v ≫ (Subobject.ofLE (FCg.fil (s + m + 1) 1)
              (FCg.fil (s + m) 1) (FCg.fil_anti (s + m) 1) ≫
              (sq.V₃.F.F (s + m) τ).arrow) ≫ sq.g.aMap τ := by rw [hinc]
        _ = (v ≫ Subobject.ofLE (FCg.fil (s + m + 1) 1)
              (FCg.fil (s + m) 1) (FCg.fil_anti (s + m) 1)) ≫
              (sq.V₃.F.F (s + m) τ).arrow ≫ sq.g.aMap τ := by
                simp only [Category.assoc]
        _ = (zl_g - z₀) ≫ (sq.V₃.F.F (s + m) τ).arrow ≫
              sq.g.aMap τ := by rw [hv]
    have hmap : FCg.d 1 = sq.g.aMap τ := by
      simp [FCg, unboundedUnderlyingComplex, underlyingComplex,
        twoTermDiff, twoTermObj]
    rw [hmap]
    change (sq.V₄.F.F (s + n + kval) τ).Factors
      (v ≫ (sq.V₃.F.F (s + m + 1) τ).arrow ≫ sq.g.aMap τ)
    rw [hvambient]
    exact hgDiffRange
  obtain ⟨wg, hdg, hwg⟩ := unbounded_uniform_detection_from_reference
    sq.g τ l hl (s + m) 1 (s + n + kval) (by omega)
      hg hg_nc z₀ zl_g w₀ hz₀ hz_g hdg₀ v hv hgVRange
  have hgambient := unbounded_lift_ambient_map sq.g τ
    (s + m) (s + m + l) (by omega) zl_g wg hdg
  change zl ≫ (sq.V₃.F.F (s + m) τ).arrow ≫ sq.g.aMap τ =
    wg ≫ (sq.V₄.F.F (s + m + l) τ).arrow at hgambient
  have hqgambient : yl ≫ (sq.V₂.F.F (s + n) τ).arrow ≫ sq.q.aMap τ =
      wg ≫ (sq.V₄.F.F (s + m + l) τ).arrow :=
    hsquare.trans hgambient
  let FCq := unboundedUnderlyingComplex sq.q τ
  have hqfil : yl ≫ FCq.filDiff (s + n) 1 =
      wg ≫ Subobject.ofLE (FCq.fil (s + m + l) 0)
        (FCq.fil (s + n) 0) (FCq.fil_anti_of_le 0 (by omega)) := by
    exact unbounded_filDiff_of_ambient_map sq.q τ
      (s + n) (s + m + l) (by omega) yl wg hqgambient
  have hwq : UnboundedExtensionIsLift sq.q τ (s + m + l) 0 wg w :=
    unboundedExtensionIsLift_target_independent sq.g sq.q τ
      (s + m + l) wg w hwg
  exact unboundedDifferentialRelation_of_lift_at_target sq.q τ
    (m + l - n) (by omega) (s + n) (s + m + l) 1 (by ring)
      hyq hwq hqfil

/-- 无界版普通无 crossing 推论：若 `g` 边本身无 crossing，则无需额外的
范围参数及 `q` 边零关系。 -/
theorem unboundedEssCommutativity_noCrossing
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {ω' : Type w}
    (sq : ConvergingSSSquare (C := C) (ω := ω) (ω' := ω'))
    (n m l s : ℤ) (τ : ω')
    (hn : 0 ≤ n) (hm : 0 ≤ m) (hl : 0 ≤ l)
    (hr : 0 ≤ m + l - n)
    {T : C} [Projective T]
    (x : T ⟶ (sq.V₁.E.ssData
      (sq.V₁.conv.reindexEquiv.symm (s, τ))).eInfty)
    (y : T ⟶ (sq.V₂.E.ssData
      (sq.V₂.conv.reindexEquiv.symm (s + n, τ))).eInfty)
    (z : T ⟶ (sq.V₃.E.ssData
      (sq.V₃.conv.reindexEquiv.symm (s + m, τ))).eInfty)
    (w : T ⟶ (sq.V₄.E.ssData
      (sq.V₄.conv.reindexEquiv.symm (s + m + l, τ))).eInfty)
    (hf : DifferentialRelation (ExtensionSpectralSequence sq.f τ)
      n (s, 1) x y)
    (hp : DifferentialRelation (ExtensionSpectralSequence sq.p τ)
      m (s, 1) x z)
    (hf_or_p_nc : ESSRelationNoCrossing n (s, 1) hf ∨
      ESSRelationNoCrossing m (s, 1) hp)
    (hg : DifferentialRelation (ExtensionSpectralSequence sq.g τ)
      l (s + m, 1) z w)
    (hg_nc : ESSRelationNoCrossing l (s + m, 1) hg) :
    DifferentialRelation (ExtensionSpectralSequence sq.q τ)
      (m + l - n) (s + n, 1) y
      (Eq.mpr (congrArg (fun X : C => T ⟶ X)
        (unbounded_comm_target_eq sq n m l s τ)) w) := by
  obtain ⟨xl, yl, zl, _hx, hy, hz, hdy, hdz⟩ :=
    unbounded_comm_common_source_lift sq n m s τ hn hm x y z
      hf hp hf_or_p_nc
  have hsquare := unbounded_comm_lift_square_ambient
    sq n m s τ hn hm xl yl zl hdy hdz
  have hyq : UnboundedExtensionIsLift sq.q τ (s + n) 1 yl y :=
    unboundedExtensionIsLift_target_source sq.f sq.q τ (s + n) yl y hy
  let zl_g : T ⟶ Subobject.underlying.obj
      ((unboundedUnderlyingComplex sq.g τ).fil (s + m) 1) := zl
  have hz_g : UnboundedExtensionIsLift sq.g τ (s + m) 1 zl_g z :=
    unboundedExtensionIsLift_target_source sq.p sq.g τ (s + m) zl z hz
  obtain ⟨wg, hdg, hwg⟩ := unbounded_uniform_detection
    sq.g τ l hl (s + m) 1 hg hg_nc zl_g hz_g
  have hgambient := unbounded_lift_ambient_map sq.g τ
    (s + m) (s + m + l) (by omega) zl_g wg hdg
  change zl ≫ (sq.V₃.F.F (s + m) τ).arrow ≫ sq.g.aMap τ =
    wg ≫ (sq.V₄.F.F (s + m + l) τ).arrow at hgambient
  change yl ≫ (sq.V₂.F.F (s + n) τ).arrow ≫ sq.q.aMap τ =
    zl ≫ (sq.V₃.F.F (s + m) τ).arrow ≫ sq.g.aMap τ at hsquare
  have ha : yl ≫ (sq.V₂.F.F (s + n) τ).arrow ≫ sq.q.aMap τ =
      wg ≫ (sq.V₄.F.F (s + m + l) τ).arrow := hsquare.trans hgambient
  have hwq : UnboundedExtensionIsLift sq.q τ (s + m + l) 0 wg w :=
    unboundedExtensionIsLift_target_independent sq.g sq.q τ
      (s + m + l) wg w hwg
  exact unboundedDifferentialRelation_of_ambient_map sq.q τ
    (m + l - n) hr (s + n) (s + m + l) (by ring)
      yl wg hyq hwq ha

/-- 无界版三角形推论：在 `f ≫ q = p` 时，左边两条关系传播为
`d_{m-n}^q(y)=z`。 -/
theorem unboundedEssCommutativity_triangle
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {ω' : Type w}
    (V₁ V₂ V₃ : ConvergingSS (C := C) (ω := ω) (ω' := ω'))
    (f : V₁ ⟶ V₂) (p : V₁ ⟶ V₃) (q : V₂ ⟶ V₃)
    (hcomm : f ≫ q = p)
    (n m s : ℤ) (τ : ω')
    (hn : 0 ≤ n) (hm : 0 ≤ m) (hnm : n ≤ m)
    {T : C} [Projective T]
    (x : T ⟶ (V₁.E.ssData
      (V₁.conv.reindexEquiv.symm (s, τ))).eInfty)
    (y : T ⟶ (V₂.E.ssData
      (V₂.conv.reindexEquiv.symm (s + n, τ))).eInfty)
    (z : T ⟶ (V₃.E.ssData
      (V₃.conv.reindexEquiv.symm (s + m, τ))).eInfty)
    (hf : DifferentialRelation (ExtensionSpectralSequence f τ)
      n (s, 1) x y)
    (hp : DifferentialRelation (ExtensionSpectralSequence p τ)
      m (s, 1) x z)
    (hf_or_p_nc : ESSRelationNoCrossing n (s, 1) hf ∨
      ESSRelationNoCrossing m (s, 1) hp) :
    let sqtri : ConvergingSSSquare (C := C) (ω := ω) (ω' := ω') :=
      { V₁ := V₁, V₂ := V₂, V₃ := V₃, V₄ := V₃,
        f := f, p := p, q := q, g := 𝟙 V₃,
        comm := by rw [Category.comp_id]; exact hcomm }
    DifferentialRelation (ExtensionSpectralSequence q τ)
      (m - n) (s + n, 1) y
      (Eq.mpr (congrArg (fun X : C => T ⟶ X)
        (show ((ExtensionSpectralSequence q τ).ssData
          ((s + n, 1) + (ExtensionSpectralSequence q τ).diffDeg (m - n))).V =
          (V₃.E.ssData (V₃.conv.reindexEquiv.symm (s + m, τ))).eInfty by
            have hi : ((s + n, 1) + (ExtensionSpectralSequence q τ).diffDeg
              (m - n) : ℤ × ℤ) = (s + m, 0) := by
              rw [ExtensionSpectralSequence_diffDeg]
              ext <;> simp <;> ring
            rw [hi]
            rfl)) z) := by
  dsimp only
  let sqtri : ConvergingSSSquare (C := C) (ω := ω) (ω' := ω') :=
    { V₁ := V₁, V₂ := V₂, V₃ := V₃, V₄ := V₃,
      f := f, p := p, q := q, g := 𝟙 V₃,
      comm := by rw [Category.comp_id]; exact hcomm }
  obtain ⟨xl, yl, zl, _hx, hy, hz, hdy, hdz⟩ :=
    unbounded_comm_common_source_lift sqtri n m s τ hn hm x y z
      hf hp hf_or_p_nc
  have hsquare := unbounded_comm_lift_square_ambient
    sqtri n m s τ hn hm xl yl zl hdy hdz
  have hyq : UnboundedExtensionIsLift q τ (s + n) 1 yl y :=
    unboundedExtensionIsLift_target_source f q τ (s + n) yl y hy
  have hzq : UnboundedExtensionIsLift q τ (s + m) 0 zl z :=
    unboundedExtensionIsLift_target_independent p q τ (s + m) zl z hz
  have ha : yl ≫ (V₂.F.F (s + n) τ).arrow ≫ q.aMap τ =
      zl ≫ (V₃.F.F (s + m) τ).arrow := by
    change yl ≫ (V₂.F.F (s + n) τ).arrow ≫ q.aMap τ =
      zl ≫ (V₃.F.F (s + m) τ).arrow ≫ sqtri.g.aMap τ at hsquare
    have hgid : sqtri.g.aMap τ = 𝟙 (V₃.A τ) := rfl
    rw [hgid, Category.comp_id] at hsquare
    exact hsquare
  exact unboundedDifferentialRelation_of_ambient_map q τ
    (m - n) (by omega) (s + n) (s + m) (by ring)
      yl zl hyq hzq ha

/-- 无界版复合推论：若 `p ≫ g = q`，则 `p` 边与无 crossing 的 `g`
边关系复合为 `q` 边上的 `d_{m+l}` 关系。 -/
theorem unboundedEssCommutativity_composition
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {ω' : Type w}
    (V₁ V₃ V₄ : ConvergingSS (C := C) (ω := ω) (ω' := ω'))
    (p : V₁ ⟶ V₃) (g : V₃ ⟶ V₄) (q : V₁ ⟶ V₄)
    (hcomm : p ≫ g = q)
    (m l s : ℤ) (τ : ω') (hm : 0 ≤ m) (hl : 0 ≤ l)
    {T : C} [Projective T]
    (x : T ⟶ (V₁.E.ssData
      (V₁.conv.reindexEquiv.symm (s, τ))).eInfty)
    (z : T ⟶ (V₃.E.ssData
      (V₃.conv.reindexEquiv.symm (s + m, τ))).eInfty)
    (w : T ⟶ (V₄.E.ssData
      (V₄.conv.reindexEquiv.symm (s + m + l, τ))).eInfty)
    (hp : DifferentialRelation (ExtensionSpectralSequence p τ)
      m (s, 1) x z)
    (hg : DifferentialRelation (ExtensionSpectralSequence g τ)
      l (s + m, 1) z w)
    (hg_nc : ESSRelationNoCrossing l (s + m, 1) hg) :
    let sqcomp : ConvergingSSSquare (C := C) (ω := ω) (ω' := ω') :=
      { V₁ := V₁, V₂ := V₁, V₃ := V₃, V₄ := V₄,
        f := 𝟙 V₁, p := p, q := q, g := g,
        comm := by rw [Category.id_comp]; exact hcomm.symm }
    DifferentialRelation (ExtensionSpectralSequence q τ)
      (m + l) (s, 1) x
      (Eq.mpr (congrArg (fun X : C => T ⟶ X)
        (show ((ExtensionSpectralSequence q τ).ssData
          ((s, 1) + (ExtensionSpectralSequence q τ).diffDeg (m + l))).V =
          (V₄.E.ssData (V₄.conv.reindexEquiv.symm (s + m + l, τ))).eInfty by
            have hi : ((s, 1) + (ExtensionSpectralSequence q τ).diffDeg
              (m + l) : ℤ × ℤ) = (s + m + l, 0) := by
              rw [ExtensionSpectralSequence_diffDeg]
              ext <;> simp <;> ring
            rw [hi]
            rfl)) w) := by
  dsimp only
  let sqcomp : ConvergingSSSquare (C := C) (ω := ω) (ω' := ω') :=
    { V₁ := V₁, V₂ := V₁, V₃ := V₃, V₄ := V₄,
      f := 𝟙 V₁, p := p, q := q, g := g,
      comm := by rw [Category.id_comp]; exact hcomm.symm }
  obtain ⟨xl, zl, hx, hz, hdz⟩ :=
    unbounded_lift_of_differentialRelation p τ m hm s 1 hp
  let zl_g : T ⟶ Subobject.underlying.obj
      ((unboundedUnderlyingComplex g τ).fil (s + m) 1) := zl
  have hz_g : UnboundedExtensionIsLift g τ (s + m) 1 zl_g z :=
    unboundedExtensionIsLift_target_source p g τ (s + m) zl z hz
  obtain ⟨wg, hdg, hwg⟩ := unbounded_uniform_detection
    g τ l hl (s + m) 1 hg hg_nc zl_g hz_g
  have hpambient := unbounded_lift_ambient_map p τ
    s (s + m) (by omega) xl zl hdz
  have hgambient := unbounded_lift_ambient_map g τ
    (s + m) (s + m + l) (by omega) zl_g wg hdg
  change xl ≫ (V₁.F.F s τ).arrow ≫ p.aMap τ =
    zl ≫ (V₃.F.F (s + m) τ).arrow at hpambient
  change zl ≫ (V₃.F.F (s + m) τ).arrow ≫ g.aMap τ =
    wg ≫ (V₄.F.F (s + m + l) τ).arrow at hgambient
  have ha : xl ≫ (V₁.F.F s τ).arrow ≫ q.aMap τ =
      wg ≫ (V₄.F.F (s + m + l) τ).arrow := by
    have hqa : q.aMap τ = p.aMap τ ≫ g.aMap τ := by
      change q.aMap τ = (p ≫ g).aMap τ
      exact congrArg (fun h : V₁ ⟶ V₄ => h.aMap τ) hcomm.symm
    calc
      xl ≫ (V₁.F.F s τ).arrow ≫ q.aMap τ =
          xl ≫ (V₁.F.F s τ).arrow ≫ p.aMap τ ≫ g.aMap τ := by rw [hqa]
      _ = (xl ≫ (V₁.F.F s τ).arrow ≫ p.aMap τ) ≫ g.aMap τ := by
        simp only [Category.assoc]
      _ = zl ≫ (V₃.F.F (s + m) τ).arrow ≫ g.aMap τ := by
        simpa only [Category.assoc] using
          congrArg (fun u : T ⟶ V₃.A τ => u ≫ g.aMap τ) hpambient
      _ = wg ≫ (V₄.F.F (s + m + l) τ).arrow := hgambient
  have hxq : UnboundedExtensionIsLift q τ s 1 xl x :=
    unboundedExtensionIsLift_source_independent p q τ s xl x hx
  have hwq : UnboundedExtensionIsLift q τ (s + m + l) 0 wg w :=
    unboundedExtensionIsLift_target_independent g q τ
      (s + m + l) wg w hwg
  exact unboundedDifferentialRelation_of_ambient_map q τ
    (m + l) (by omega) s (s + m + l) (by ring)
      xl wg hxq hwq ha

end KIPBase.SpectralSequence
