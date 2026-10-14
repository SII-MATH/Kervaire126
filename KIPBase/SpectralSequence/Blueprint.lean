/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import KIPBase.SpectralSequence.Exactness
import KIPBase.SpectralSequence.MorphismCriterion
import KIPBase.SpectralSequence.ShiftedDifferential

/-!
# 谱序列 Blueprint 接口

本文件把 `SpectralSequence` 目录中已经证明的底层构造封装成 Blueprint
使用的接口。这里不改变 `SSData`、`PreSS` 或过滤复形的基础定义；所有
元素式条件仍然通过 `SSData` 的嵌套子对象 `Z`、`B` 表述。
-/

namespace KIPBase.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v w

set_option linter.dupNamespace false

variable {C : Type u} [Category.{v} C] [Abelian C]

/-! ## 完备、穷尽与 Hausdorff 过滤 -/

/-- Blueprint 中“完备且分离的穷尽过滤”的统一接口。

三个条件保持彼此独立：`exhaustive` 和 `hausdorff` 分别表达过滤层的并为
顶、交为底；`complete` 表达到截断逆极限的典范映射满足泛性质。特别地，
本结构不把 Hausdorff 条件误写成最终为零。 -/
structure Filtration.CompleteSeparated
    {ω : Type w} {A : ω → C} (F : Filtration A) : Prop where
  exhaustive : F.IsExhaustive
  hausdorff : F.IsHausdorff
  complete : F.IsComplete

/-! ## 页编号约定 -/

/-- 一个显示页编号约定。自然数参数就是论文中的显示页号，
只在 `firstPage ≤ n` 时要求它合法。`page` 给出 Lean 内部的整数页，
`cycleLevel` 与 `quotientExponent` 分别给出元素式 `Z/B` 层和
外部商对象所用的自然数。后两个函数相等是显式定律。 -/
structure PageLevelConvention where
  firstPage : ℕ
  page : ℕ → ℤ
  cycleLevel : ℕ → ℕ
  quotientExponent : ℕ → ℕ
  page_first : page firstPage = firstPage
  page_lower_bound : ∀ n, firstPage ≤ n → (firstPage : ℤ) ≤ page n
  page_succ : ∀ n, firstPage ≤ n → page (n + 1) = page n + 1
  cycleLevel_succ : ∀ n, firstPage ≤ n →
    cycleLevel (n + 1) = cycleLevel n + 1
  quotientExponent_succ : ∀ n, firstPage ≤ n →
    quotientExponent (n + 1) = quotientExponent n + 1
  levels_agree : cycleLevel = quotientExponent

/-- AIM 的 Adams 显示约定：显示页从 `2` 开始；对 `n ≥ 2`，
显示页 `E_n` 就是 Lean 的整数页 `n`，并由 `Z_(n-1)/B_(n-1)`
给出；合成商指数同样是 `n-1`。 -/
def adamsPageLevelConvention : PageLevelConvention where
  firstPage := 2
  page n := n
  cycleLevel n := n - 1
  quotientExponent n := n - 1
  page_first := by norm_num
  page_lower_bound := by intro n hn; exact_mod_cast hn
  page_succ := by intro n _; omega
  cycleLevel_succ := by intro n hn; omega
  quotientExponent_succ := by intro n hn; omega
  levels_agree := rfl

/-! ## 带重指标的页态射 -/

/-- 带重指标的谱序列页态射。它不要求环境对象 `V` 之间存在
未移位态射，而是直接记录每个整数页上的态射。`degree_compat`
保证重指标与微分次数相容，`comm_d` 是搬运目标指标后的微分
交换式。这个类型可以表述 `(s,t) ↦ (s+k,t+k+d)` 一类仿射平移。 -/
structure ReindexedSpectralSequenceMorphism
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {ι' : Type*} [AddCommGroup ι'] [DecidableEq ι']
    (E : SpectralSequence C ι) (E' : SpectralSequence C ι') where
  reindex : ι → ι'
  r₀_eq : E.r₀ = E'.r₀
  degree_compat : ∀ (r : ℤ) (k : ι),
    reindex (k + E.diffDeg r) = reindex k + E'.diffDeg r
  pageMap : ∀ (r : ℤ) (k : ι), E.Page r k ⟶ E'.Page r (reindex k)
  comm_d : ∀ (r : ℤ) (k : ι),
    pageMap r k ≫ E'.d r (reindex k) =
      E.d r k ≫ pageMap r (k + E.diffDeg r) ≫
        eqToHom (congrArg (E'.Page r) (degree_compat r k))

/-- 重指标页态射在指标 `k` 处的微分交换式。这个单独命名的
定理用于 Blueprint 中直接引用，避免使用时展开结构字段。 -/
theorem ReindexedSpectralSequenceMorphism.differential_comm
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {ι' : Type*} [AddCommGroup ι'] [DecidableEq ι']
    {E : SpectralSequence C ι} {E' : SpectralSequence C ι'}
    (f : ReindexedSpectralSequenceMorphism E E') (r : ℤ) (k : ι) :
    f.pageMap r k ≫ E'.d r (f.reindex k) =
      E.d r k ≫ f.pageMap r (k + E.diffDeg r) ≫
        eqToHom (congrArg (E'.Page r) (f.degree_compat r k)) :=
  f.comm_d r k

/-- 整数页编号取自然数时，显示页同构就是底层有限页同构。 -/
theorem FilteredComplex.shiftFiltrationSpectralSequencePageIso_nat
    (FC : FilteredComplex C) (bnd : FC.IsBounded) (a : ℤ)
    (n : ℕ) (sk : ℤ × ℤ) :
    FC.shiftFiltrationSpectralSequencePageIso bnd a (n : ℤ) sk =
      FC.shiftFiltrationPageIso bnd a sk n := by
  rfl

/-- 平移过滤复形的谱序列按 `(s,k) ↦ (s+a,k)` 重指标后
规范地映到原谱序列。微分交换性由有限页上的核代表元证明给出；
负页上两边的微分均为零。 -/
noncomputable def FilteredComplex.shiftFiltrationReindexedMorphism
    (FC : FilteredComplex C) (bnd : FC.IsBounded) (a : ℤ) :
    ReindexedSpectralSequenceMorphism
      ((FC.shiftFiltration a).toSpectralSequence (bnd.shiftFiltration a))
      (FC.toSpectralSequence bnd) where
  reindex := fun sk => (sk.1 + a, sk.2)
  r₀_eq := rfl
  degree_compat := fun r sk =>
    (FC.shiftFiltration_degree_compat bnd a r sk).symm
  pageMap := fun r sk =>
    (FC.shiftFiltrationSpectralSequencePageIso bnd a r sk).hom
  comm_d := by
    intro r ⟨s, k⟩
    by_cases hr : 0 ≤ r
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hr
      change (FC.shiftFiltrationSpectralSequencePageIso bnd a
          (n : ℤ) (s, k)).hom ≫
          (FC.toPreSS bnd).d (n : ℤ) (s + a, k) =
        ((FC.shiftFiltration a).toPreSS (bnd.shiftFiltration a)).d
            (n : ℤ) (s, k) ≫
          (FC.shiftFiltrationSpectralSequencePageIso bnd a (n : ℤ)
            (s + (n : ℤ), k - 1)).hom ≫
          eqToHom (congrArg
            (fun q : ℤ => (FC.toSSData bnd q (k - 1)).page
              (n : WithTop ℕ))
            (show (s + (n : ℤ)) + a = (s + a) + (n : ℤ) by abel))
      rw [FC.shiftFiltrationSpectralSequencePageIso_nat bnd a n (s, k),
        FC.shiftFiltrationSpectralSequencePageIso_nat bnd a n
          (s + (n : ℤ), k - 1)]
      dsimp only [FilteredComplex.toPreSS]
      simp only [dif_pos (Int.natCast_nonneg n)]
      erw [eqToHom_refl, Category.id_comp, eqToHom_refl,
        Category.comp_id, eqToHom_refl, Category.id_comp,
        eqToHom_refl, Category.comp_id]
      change (FC.shiftFiltrationPageIso bnd a (s, k) n).hom ≫
          FC.pageDifferential bnd (s + a) k n =
        (FC.shiftFiltration a).pageDifferential
            (bnd.shiftFiltration a) s k n ≫
          (FC.shiftFiltrationPageIso bnd a
            (s + (n : ℤ), k - 1) n).hom ≫
          eqToHom (congrArg
            (fun q : ℤ => (FC.toSSData bnd q (k - 1)).page
              (n : WithTop ℕ))
            (show (s + (n : ℤ)) + a = (s + a) + (n : ℤ) by abel))
      exact FC.shiftFiltrationPageIso_comm_pageDifferential bnd a s k n
    · change _ ≫ (FC.toPreSS bnd).d r (s + a, k) =
        ((FC.shiftFiltration a).toPreSS
          (bnd.shiftFiltration a)).d r (s, k) ≫ _
      dsimp only [FilteredComplex.toPreSS]
      simp only [dif_neg hr, comp_zero, zero_comp]

/-- 带过滤平移的复形态射在谱序列上诱导重指标态射。
它先映到平移过滤的目标，再复合上一条的规范重指标态射。 -/
noncomputable def ShiftedFilteredComplexMorphism.toReindexedSpectralSequenceMorphism
    {FC₁ FC₂ : FilteredComplex C} {a : ℤ}
    (f : ShiftedFilteredComplexMorphism FC₁ FC₂ a)
    (bnd₁ : FC₁.IsBounded) (bnd₂ : FC₂.IsBounded) :
    ReindexedSpectralSequenceMorphism
      (FC₁.toSpectralSequence bnd₁) (FC₂.toSpectralSequence bnd₂) where
  reindex := fun sk => (sk.1 + a, sk.2)
  r₀_eq := rfl
  degree_compat := fun r sk =>
    (FC₂.shiftFiltration_degree_compat bnd₂ a r sk).symm
  pageMap := fun r sk =>
    let F := f.toSpectralSequenceMorphism bnd₁ bnd₂
    let S := FC₂.shiftFiltrationReindexedMorphism bnd₂ a
    let n₁ : WithTop ℕ :=
      ↑(r - (FC₁.toSpectralSequence bnd₁).r₀).toNat
    let n₂ : WithTop ℕ :=
      ↑(r - ((FC₂.shiftFiltration a).toSpectralSequence
        (bnd₂.shiftFiltration a)).r₀).toNat
    let hn : n₁ = n₂ := congrArg
      (fun r₀ => (↑(r - r₀).toNat : WithTop ℕ)) F.r₀_eq
    F.pageMapOfEq sk sk rfl n₁ n₂ hn ≫ S.pageMap r sk
  comm_d := by
    intro r sk
    let F := f.toSpectralSequenceMorphism bnd₁ bnd₂
    let S := FC₂.shiftFiltrationReindexedMorphism bnd₂ a
    let E₁ := FC₁.toSpectralSequence bnd₁
    let E₂ := (FC₂.shiftFiltration a).toSpectralSequence
      (bnd₂.shiftFiltration a)
    let n₁ : WithTop ℕ := ↑(r - E₁.r₀).toNat
    let n₂ : WithTop ℕ := ↑(r - E₂.r₀).toNat
    let hn : n₁ = n₂ := congrArg
      (fun r₀ => (↑(r - r₀).toNat : WithTop ℕ)) F.r₀_eq
    let hk : sk + E₁.diffDeg r = sk + E₂.diffDeg r :=
      congrArg (fun d => sk + d) (congrFun F.diffDeg_eq r)
    let sourceMap := F.pageMapOfEq sk sk rfl n₁ n₂ hn
    let targetMap := F.pageMapOfEq
      (sk + E₁.diffDeg r) (sk + E₂.diffDeg r) hk n₁ n₂ hn
    have hF := F.comm_d r sk
    have hS := S.comm_d r sk
    change sourceMap ≫ E₂.d r sk = E₁.d r sk ≫ targetMap at hF
    change S.pageMap r sk ≫
        (FC₂.toSpectralSequence bnd₂).d r (S.reindex sk) =
      E₂.d r sk ≫ S.pageMap r (sk + E₂.diffDeg r) ≫
        eqToHom (congrArg ((FC₂.toSpectralSequence bnd₂).Page r)
          (S.degree_compat r sk)) at hS
    change (sourceMap ≫ S.pageMap r sk) ≫
        (FC₂.toSpectralSequence bnd₂).d r (S.reindex sk) =
      E₁.d r sk ≫
        (targetMap ≫ S.pageMap r (sk + E₂.diffDeg r)) ≫
        eqToHom (congrArg ((FC₂.toSpectralSequence bnd₂).Page r)
          (S.degree_compat r sk))
    calc
      (sourceMap ≫ S.pageMap r sk) ≫
          (FC₂.toSpectralSequence bnd₂).d r (S.reindex sk) =
        sourceMap ≫ (S.pageMap r sk ≫
          (FC₂.toSpectralSequence bnd₂).d r (S.reindex sk)) :=
        Category.assoc _ _ _
      _ = sourceMap ≫ (E₂.d r sk ≫
          S.pageMap r (sk + E₂.diffDeg r) ≫
          eqToHom (congrArg ((FC₂.toSpectralSequence bnd₂).Page r)
            (S.degree_compat r sk))) := by rw [hS]
      _ = (sourceMap ≫ E₂.d r sk) ≫
          S.pageMap r (sk + E₂.diffDeg r) ≫
          eqToHom (congrArg ((FC₂.toSpectralSequence bnd₂).Page r)
            (S.degree_compat r sk)) := by simp only [Category.assoc]
      _ = (E₁.d r sk ≫ targetMap) ≫
          S.pageMap r (sk + E₂.diffDeg r) ≫
          eqToHom (congrArg ((FC₂.toSpectralSequence bnd₂).Page r)
            (S.degree_compat r sk)) := by rw [hF]
      _ = E₁.d r sk ≫
          (targetMap ≫ S.pageMap r (sk + E₂.diffDeg r)) ≫
          eqToHom (congrArg ((FC₂.toSpectralSequence bnd₂).Page r)
            (S.degree_compat r sk)) := by simp only [Category.assoc]

/-- 交换方块的两条竖边若具有同一过滤次数 `a`，则它们在
`f`-ESS 与 `g`-ESS 之间诱导真正的重指标谱序列态射。 -/
noncomputable def HomotopyCommSquare.shiftedESSReindexedMorphism
    {j : Type w} [AddCommGroup j] [DecidableEq j] {o : Type w}
    {E₁ E₂ E₃ E₄ : SpectralSequence C j}
    {A₁ A₂ A₃ A₄ : o → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {F₃ : Filtration A₃} {F₄ : Filtration A₄}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {conv₃ : Convergence E₃ A₃ F₃} {conv₄ : Convergence E₄ A₄ F₄}
    (sq : HomotopyCommSquare conv₁ conv₂ conv₃ conv₄)
    (a : ℤ) (ha : sq.FiltrationShiftData a) (t : o) :
    ReindexedSpectralSequenceMorphism (sq.extf.ess t) (sq.extg.ess t) := by
  change ReindexedSpectralSequenceMorphism
    ((sq.extf.complex t).toSpectralSequence (sq.extf.bounded t))
    ((sq.extg.complex t).toSpectralSequence (sq.extg.bounded t))
  exact (sq.shiftedESSFilteredComplexMorphism a ha t).toReindexedSpectralSequenceMorphism
    (sq.extf.bounded t) (sq.extg.bounded t)

/-! ## 元素式循环、边缘与永久类 -/

/-- 环境对象中的广义元素在第 `r` 层是循环。 -/
def SSData.IsCycleAt (D : SSData C) (r : WithTop ℕ) {T : C}
    (x : T ⟶ D.V) : Prop :=
  (D.Z r).Factors x

/-- 环境对象中的广义元素在第 `r` 层是边缘。 -/
def SSData.IsBoundaryAt (D : SSData C) (r : WithTop ℕ) {T : C}
    (x : T ⟶ D.V) : Prop :=
  (D.B r).Factors x

/-- 一个初始环境对象代表元生存到有限层 `r`，即它属于 `Z_r`。 -/
abbrev SSData.SurvivesThrough (D : SSData C) (r : ℕ) {T : C}
    (x : T ⟶ D.V) : Prop :=
  D.IsCycleAt (r : WithTop ℕ) x

/-- 永久代表元是属于 `Z_∞` 的环境对象广义元素。 -/
abbrev SSData.IsPermanentRepresentative (D : SSData C) {T : C}
    (x : T ⟶ D.V) : Prop :=
  D.IsCycleAt ⊤ x

/-- `x` 在第 `r` 页代表非零类：选择它到 `Z_r` 的提升后，其商投影非零。 -/
def SSData.RepresentsNonzeroAt (D : SSData C) (r : WithTop ℕ) {T : C}
    (x : T ⟶ D.V) : Prop :=
  ∃ xZ : T ⟶ Subobject.underlying.obj (D.Z r),
    xZ ≫ (D.Z r).arrow = x ∧ xZ ≫ D.pageπ r ≠ 0

/-- 对一个已经是 `r`-循环的代表元，它给出非零 `E_r` 类，当且仅当它
不是 `r`-边缘。这个结论也适用于 `r = ∞`。 -/
theorem SSData.representsNonzeroAt_iff
    (D : SSData C) (r : WithTop ℕ) {T : C}
    (x : T ⟶ D.V) (hx : D.IsCycleAt r x) :
    D.RepresentsNonzeroAt r x ↔ ¬ D.IsBoundaryAt r x := by
  constructor
  · rintro ⟨xZ, hxZ, hnonzero⟩ hboundary
    let xB := (D.B r).factorThru x hboundary
    have hxB : xB ≫ (D.B r).arrow = x :=
      (D.B r).factorThru_arrow x hboundary
    let i := Subobject.ofLE (D.B r) (D.Z r) (D.B_le_Z r)
    have hXBZ : xB ≫ i = xZ := by
      apply (cancel_mono (D.Z r).arrow).mp
      calc
        (xB ≫ i) ≫ (D.Z r).arrow = xB ≫ (D.B r).arrow := by
          simp only [Category.assoc, i, Subobject.ofLE_arrow]
        _ = x := hxB
        _ = xZ ≫ (D.Z r).arrow := hxZ.symm
    apply hnonzero
    change xZ ≫ cokernel.π i = 0
    rw [← hXBZ, Category.assoc, cokernel.condition, comp_zero]
  · intro hboundary
    let xZ := (D.Z r).factorThru x hx
    have hxZ : xZ ≫ (D.Z r).arrow = x :=
      (D.Z r).factorThru_arrow x hx
    refine ⟨xZ, hxZ, ?_⟩
    intro hzero
    let i := Subobject.ofLE (D.B r) (D.Z r) (D.B_le_Z r)
    let xB := Abelian.monoLift i xZ hzero
    apply hboundary
    apply (Subobject.factors_iff _ _).2
    refine ⟨xB, ?_⟩
    calc
      xB ≫ (D.B r).arrow = xB ≫ i ≫ (D.Z r).arrow := by
        rw [Subobject.ofLE_arrow]
      _ = xZ ≫ (D.Z r).arrow := by
        rw [← Category.assoc, Abelian.monoLift_comp]
      _ = x := by exact hxZ

/-- 永久代表元给出非零 `E_∞` 类，当且仅当它不属于 `B_∞`。 -/
theorem SSData.permanent_nonzero_iff
    (D : SSData C) {T : C} (x : T ⟶ D.V)
    (hx : D.IsPermanentRepresentative x) :
    D.RepresentsNonzeroAt ⊤ x ↔ ¬ D.IsBoundaryAt ⊤ x :=
  D.representsNonzeroAt_iff ⊤ x hx

/-! ## 过滤复形微分关系的代表元刻画 -/

/-- Blueprint 的“扩张当且仅当存在相容代表元”的过滤复形版本。
正向需要测试对象投射，以便把商页上的广义元素提升回过滤层；反向不需要
额外选择。 -/
theorem FilteredComplex.differentialRelation_iff_lifts
    (FC : FilteredComplex C) (bnd : FC.IsBounded)
    (r : ℤ) (hr : 0 ≤ r) (s k : ℤ) {T : C} [Projective T]
    {x : T ⟶ FC.assocGraded s k}
    {y : T ⟶ FC.assocGraded (s + r) (k - 1)} :
    DifferentialRelation (FC.toSpectralSequence bnd) r (s, k) x y ↔
      ∃ (xl : T ⟶ Subobject.underlying.obj (FC.fil s k))
        (yl : T ⟶ Subobject.underlying.obj (FC.fil (s + r) (k - 1))),
        FC.IsLift s k xl x ∧ FC.IsLift (s + r) (k - 1) yl y ∧
          xl ≫ FC.filDiff s k =
            yl ≫ Subobject.ofLE (FC.fil (s + r) (k - 1))
              (FC.fil s (k - 1))
              (FC.fil_anti_of_le (k - 1) (by omega)) := by
  constructor
  · exact FC.lift_of_differentialRelation bnd r hr s k
  · rintro ⟨xl, yl, hx, hy, hd⟩
    exact FC.differentialRelation_of_lift bnd r hr s k hx hy hd

/-! ## 一般 crossing 与本质 crossing -/

/-- Blueprint 原始意义下的范围 crossing：允许见证关系本身非本质，
但要求目标广义元素非零，且目标过滤位于 `[p,s+r]`。
源复形次数固定为 `k`：对两项 ESS 而言，这正是说 crossing
仍从源项次数 `1` 出发。 -/
def FilteredComplex.GeneralCrossingRange
    (FC : FilteredComplex C) (bnd : FC.IsBounded)
    (r s k p : ℤ) {T : C} [Projective T]
    {x : T ⟶ FC.assocGraded s k}
    {y : T ⟶ FC.assocGraded (s + r) (k - 1)}
    (_h : DifferentialRelation (FC.toSpectralSequence bnd) r (s, k) x y) : Prop :=
  ∃ (u : ℤ) (m : ℕ)
      (x' : T ⟶ FC.assocGraded u k)
      (y' : T ⟶ FC.assocGraded (u + m) (k - 1)),
    s < u ∧
    DifferentialRelation (FC.toSpectralSequence bnd) (m : ℤ)
        (u, k) x' y' ∧
      y' ≠ 0 ∧ p ≤ u + m ∧ u + m ≤ s + r

/-- 不带范围限定的 crossing，下界取源过滤的下一层 `s+1`。 -/
abbrev FilteredComplex.GeneralCrossing
    (FC : FilteredComplex C) (bnd : FC.IsBounded)
    (r s k : ℤ) {T : C} [Projective T]
    {x : T ⟶ FC.assocGraded s k}
    {y : T ⟶ FC.assocGraded (s + r) (k - 1)}
    (h : DifferentialRelation (FC.toSpectralSequence bnd) r (s, k) x y) : Prop :=
  FC.GeneralCrossingRange bnd r s k (s + 1) h

/-- 范围内的一般 crossing 可以替换成同一范围内、同一复形次数
上的本质 crossing。 -/
theorem FilteredComplex.generalCrossingRange_to_essential
    (FC : FilteredComplex C) (bnd : FC.IsBounded)
    (r s k p : ℤ) {T : C} [Projective T]
    {x : T ⟶ FC.assocGraded s k}
    {y : T ⟶ FC.assocGraded (s + r) (k - 1)}
    (h : DifferentialRelation (FC.toSpectralSequence bnd) r (s, k) x y)
    (hc : FC.GeneralCrossingRange bnd r s k p h) :
    ∃ (u : ℤ) (m : ℕ)
        (x' : T ⟶ FC.assocGraded u k)
        (y' : T ⟶ FC.assocGraded (u + m) (k - 1)),
      s < u ∧
      EssentialDifferentialRelation (FC.toSpectralSequence bnd) (m : ℤ)
          (u, k) x' y' ∧
        p ≤ u + m ∧ u + m ≤ s + r := by
  classical
  rcases hc with ⟨u₀, m, x', y', hsource₀, hrel, hy', hlower, hupper⟩
  by_cases hess : EssentialDifferentialRelation (FC.toSpectralSequence bnd)
      (m : ℤ) (u₀, k) x' y'
  · exact ⟨u₀, m, x', y', hsource₀, hess, hlower, hupper⟩
  · have hb : Subobject.Factors
        (FC.boundarySubobject (u₀ + m) (k - 1) (m : WithTop ℕ)) y' := by
      have hb₀ := hess
      unfold EssentialDifferentialRelation at hb₀
      simp only [hrel, true_and, not_not] at hb₀
      change Subobject.Factors
        ((FC.toSSData bnd (u₀ + m) (k - 1)).B (m : WithTop ℕ)) y' at hb₀
      exact hb₀
    obtain ⟨u, j, huj, z, hsource, hz⟩ :=
      FC.essential_ancestor_of_nonzero_boundary bnd k m u₀
        (u₀ + m) (by omega) y' hy' hb
    refine ⟨u, j, z, _, hsource₀.trans hsource, hz, ?_, ?_⟩
    · rw [huj]
      exact hlower
    · rw [huj]
      exact hupper

/-- 范围内的本质 crossing。这是证明中使用的有限下降后正规形。 -/
def FilteredComplex.EssentialCrossingRange
    (FC : FilteredComplex C) (bnd : FC.IsBounded)
    (r s k p : ℤ) {T : C} [Projective T]
    {x : T ⟶ FC.assocGraded s k}
    {y : T ⟶ FC.assocGraded (s + r) (k - 1)}
    (_h : DifferentialRelation (FC.toSpectralSequence bnd) r (s, k) x y) : Prop :=
  ∃ (u : ℤ) (m : ℕ)
      (x' : T ⟶ FC.assocGraded u k)
      (y' : T ⟶ FC.assocGraded (u + m) (k - 1)),
    s < u ∧
      EssentialDifferentialRelation (FC.toSpectralSequence bnd) (m : ℤ)
        (u, k) x' y' ∧
      p ≤ u + m ∧ u + m ≤ s + r

/-- 指定过滤范围内没有一般 crossing。 -/
def FilteredComplex.NoGeneralCrossingRange
    (FC : FilteredComplex C) (bnd : FC.IsBounded)
    (r s k p : ℤ) {T : C} [Projective T]
    {x : T ⟶ FC.assocGraded s k}
    {y : T ⟶ FC.assocGraded (s + r) (k - 1)}
    (h : DifferentialRelation (FC.toSpectralSequence bnd) r (s, k) x y) : Prop :=
  ¬ FC.GeneralCrossingRange bnd r s k p h

/-- “没有一般 crossing”等价于“没有本质 crossing”。正向是
有限下降引理，反向使用本质目标必非零。 -/
theorem FilteredComplex.noGeneralCrossingRange_iff_noEssential
    (FC : FilteredComplex C) (bnd : FC.IsBounded)
    (r s k p : ℤ) {T : C} [Projective T]
    {x : T ⟶ FC.assocGraded s k}
    {y : T ⟶ FC.assocGraded (s + r) (k - 1)}
    (h : DifferentialRelation (FC.toSpectralSequence bnd) r (s, k) x y) :
    FC.NoGeneralCrossingRange bnd r s k p h ↔
      ¬ FC.EssentialCrossingRange bnd r s k p h := by
  constructor
  · intro hno hess
    rcases hess with ⟨u, m, x', y', hu, hrel, hlower, hupper⟩
    apply hno
    refine ⟨u, m, x', y', hu, hrel.1, ?_, hlower, hupper⟩
    intro hy
    subst y'
    exact hrel.2 Subobject.factors_zero
  · intro hno hc
    exact hno (FC.generalCrossingRange_to_essential bnd r s k p h hc)

/- 同次数的范围无 crossing 已足以控制高过滤源的微分像。若该像没有
   进入原目标层的下一层，取其最大过滤次数；对应的非零领先项本身就是
   一个被排除的一般 crossing，因此这里不需要预先假设它是本质关系。 -/
theorem FilteredComplex.NoGeneralCrossingRange.higher_source_image_deeper
    (FC : FilteredComplex C) (bnd : FC.IsBounded)
    (r s k p : ℤ) {T : C} [Projective T]
    {x : T ⟶ FC.assocGraded s k}
    {y : T ⟶ FC.assocGraded (s + r) (k - 1)}
    (hrel : DifferentialRelation (FC.toSpectralSequence bnd) r (s, k) x y)
    (hno : FC.NoGeneralCrossingRange bnd r s k p hrel)
    (t : ℤ) (hst : s < t)
    (a : T ⟶ Subobject.underlying.obj (FC.fil t k))
    (hp : (FC.fil p (k - 1)).Factors
      (a ≫ (FC.fil t k).arrow ≫ FC.d k)) :
    (FC.fil (s + r + 1) (k - 1)).Factors
      (a ≫ (FC.fil t k).arrow ≫ FC.d k) := by
  classical
  let v := a ≫ (FC.fil t k).arrow ≫ FC.d k
  have hv_t : (FC.fil t (k - 1)).Factors v := by
    change (FC.fil t (k - 1)).Factors
      (a ≫ (FC.fil t k).arrow ≫ FC.d k)
    rw [← FC.filDiff_comp_arrow]
    simpa only [Category.assoc] using
      (Subobject.factors_comp_arrow (a ≫ FC.filDiff t k))
  rcases FC.factor_max_or_zero bnd p (k - 1) v hp with hz | ⟨q, hpq, hqfac, hqmax⟩
  · change (FC.fil (s + r + 1) (k - 1)).Factors v
    rw [hz]
    exact Subobject.factors_zero
  have htq : t ≤ q := by
    by_contra hn
    have hle : FC.fil t (k - 1) ≤ FC.fil (q + 1) (k - 1) :=
      FC.fil_anti_of_le (k - 1) (by omega)
    exact hqmax (Subobject.factors_of_le v hle hv_t)
  by_contra hnot
  have hqr : q < s + r + 1 := by
    by_contra hn
    have hle : FC.fil q (k - 1) ≤ FC.fil (s + r + 1) (k - 1) :=
      FC.fil_anti_of_le (k - 1) (by omega)
    exact hnot (Subobject.factors_of_le v hle hqfac)
  let b := (FC.fil q (k - 1)).factorThru v hqfac
  have hdb : a ≫ (FC.fil t k).arrow ≫ FC.d k =
      b ≫ (FC.fil q (k - 1)).arrow :=
    ((FC.fil q (k - 1)).factorThru_arrow v hqfac).symm
  let m : ℕ := (q - t).toNat
  have htm : t + (m : ℤ) = q := by
    dsimp only [m]
    omega
  have hyne : b ≫ FC.filToAssocGraded q (k - 1) ≠ 0 :=
    FC.assocGraded_ne_zero_of_maximal q (k - 1) b
      (by simpa [b, v] using hqmax)
  let hV : ((FC.toSpectralSequence bnd).ssData
      ((t, k) + (FC.toSpectralSequence bnd).diffDeg (m : ℤ))).V =
      FC.assocGraded q (k - 1) := by
    rw [← htm]
    rfl
  let H := congrArg (fun X : C => T ⟶ X) hV
  let yb : T ⟶ FC.assocGraded (t + (m : ℤ)) (k - 1) :=
    Eq.mpr H (b ≫ FC.filToAssocGraded q (k - 1))
  have hybne : yb ≠ 0 := by
    intro hyb
    apply hyne
    have hzero : Eq.mpr H (0 : T ⟶ FC.assocGraded q (k - 1)) = 0 := by
      change (congrArg (fun X : C => T ⟶ X) hV).mpr
        (0 : T ⟶ FC.assocGraded q (k - 1)) = 0
      exact (CategoryTheory.congrArg_mpr_hom_right
        (0 : T ⟶ FC.assocGraded q (k - 1)) hV).trans zero_comp
    apply (eq_mpr_bijective H).injective
    change Eq.mpr H (b ≫ FC.filToAssocGraded q (k - 1)) = 0 at hyb
    exact hyb.trans hzero.symm
  have hdbFil : a ≫ FC.filDiff t k =
      b ≫ Subobject.ofLE (FC.fil q (k - 1))
        (FC.fil t (k - 1))
        (FC.fil_anti_of_le (k - 1) (by omega)) := by
    apply (cancel_mono (FC.fil t (k - 1)).arrow).mp
    rw [Category.assoc, FC.filDiff_comp_arrow]
    rw [Category.assoc, Subobject.ofLE_arrow]
    exact hdb
  have hcross := FC.differentialRelation_of_lift_at_target bnd (m : ℤ)
    (by omega) t k q htm rfl rfl hdbFil
  change DifferentialRelation (FC.toSpectralSequence bnd) (m : ℤ)
    (t, k) (a ≫ FC.filToAssocGraded t k) yb at hcross
  apply hno
  refine ⟨t, m, a ≫ FC.filToAssocGraded t k,
    yb, hst, hcross, hybne, ?_, ?_⟩
  · simpa only [htm] using hpq
  omega

/- 同次数范围无 crossing 给出范围一致检测。证明把任意源代表元与一个
   参照代表元相减；差来自 `F^{s+1}`，上一引理迫使其微分进入完整目标层。 -/
theorem FilteredComplex.NoGeneralCrossingRange.uniformDetection
    (FC : FilteredComplex C) (bnd : FC.IsBounded)
    (r : ℤ) (hr : 0 ≤ r) (s k p : ℤ) (hp : p ≤ s + r)
    {T : C} [Projective T]
    {x : T ⟶ FC.assocGraded s k}
    {y : T ⟶ FC.assocGraded (s + r) (k - 1)}
    (hrel : DifferentialRelation (FC.toSpectralSequence bnd) r (s, k) x y)
    (hno : FC.NoGeneralCrossingRange bnd r s k p hrel) :
    UniformDetection FC bnd r hr s k p hrel := by
  classical
  intro xl hx hxp
  obtain ⟨x₀, y₀, hx₀, _hy₀, hd₀⟩ :=
    FC.lift_of_differentialRelation bnd r hr s k hrel
  obtain ⟨v, hv⟩ := FC.isLift_sub_lift s k hx hx₀
  have hinc : Subobject.ofLE (FC.fil (s + 1) k) (FC.fil s k)
      (FC.fil_anti s k) ≫ (FC.fil s k).arrow =
      (FC.fil (s + 1) k).arrow := Subobject.ofLE_arrow _
  have hvembed : v ≫ (FC.fil (s + 1) k).arrow =
      (xl - x₀) ≫ (FC.fil s k).arrow := by
    calc
      v ≫ (FC.fil (s + 1) k).arrow =
          v ≫ (Subobject.ofLE (FC.fil (s + 1) k) (FC.fil s k)
            (FC.fil_anti s k) ≫ (FC.fil s k).arrow) :=
              congrArg (fun f => v ≫ f) hinc.symm
      _ = (v ≫ Subobject.ofLE (FC.fil (s + 1) k) (FC.fil s k)
            (FC.fil_anti s k)) ≫ (FC.fil s k).arrow :=
              (Category.assoc _ _ _).symm
      _ = (xl - x₀) ≫ (FC.fil s k).arrow :=
        congrArg (fun f => f ≫ (FC.fil s k).arrow) hv
  have hx₀p : (FC.fil p (k - 1)).Factors
      (x₀ ≫ (FC.fil s k).arrow ≫ FC.d k) := by
    have htarget : (FC.fil (s + r) (k - 1)).Factors
        (x₀ ≫ (FC.fil s k).arrow ≫ FC.d k) := by
      rw [← FC.filDiff_comp_arrow, ← Category.assoc, hd₀]
      simp only [Category.assoc, Subobject.ofLE_arrow]
      exact Subobject.factors_comp_arrow y₀
    exact Subobject.factors_of_le _ (FC.fil_anti_of_le (k - 1) hp) htarget
  have hvp : (FC.fil p (k - 1)).Factors
      (v ≫ (FC.fil (s + 1) k).arrow ≫ FC.d k) := by
    have hvambient : v ≫ (FC.fil (s + 1) k).arrow ≫ FC.d k =
        (xl - x₀) ≫ (FC.fil s k).arrow ≫ FC.d k := by
      simpa only [Category.assoc] using
        congrArg (fun f => f ≫ FC.d k) hvembed
    have hsum : v ≫ (FC.fil (s + 1) k).arrow ≫ FC.d k +
        x₀ ≫ (FC.fil s k).arrow ≫ FC.d k =
        xl ≫ (FC.fil s k).arrow ≫ FC.d k := by
      rw [hvambient, Preadditive.sub_comp]
      abel
    apply Subobject.factors_left_of_factors_add
      (v ≫ (FC.fil (s + 1) k).arrow ≫ FC.d k)
      (x₀ ≫ (FC.fil s k).arrow ≫ FC.d k)
    · simpa only [hsum] using hxp
    · exact hx₀p
  have htarget := hno.higher_source_image_deeper FC bnd r s k p hrel
    (s + 1) (by omega) v hvp
  let cdeep := (FC.fil (s + r + 1) (k - 1)).factorThru
    (v ≫ (FC.fil (s + 1) k).arrow ≫ FC.d k) htarget
  let ideep := Subobject.ofLE (FC.fil (s + r + 1) (k - 1))
    (FC.fil (s + r) (k - 1)) (FC.fil_anti (s + r) (k - 1))
  let c := cdeep ≫ ideep
  let yl := y₀ + c
  have hdiff : xl ≫ FC.filDiff s k =
      yl ≫ Subobject.ofLE (FC.fil (s + r) (k - 1)) (FC.fil s (k - 1))
        (FC.fil_anti_of_le (k - 1) (by omega)) := by
    apply (cancel_mono (FC.fil s (k - 1)).arrow).mp
    simp only [Category.assoc, FC.filDiff_comp_arrow, Subobject.ofLE_arrow,
      yl, Preadditive.add_comp]
    have hreference : x₀ ≫ (FC.fil s k).arrow ≫ FC.d k =
        y₀ ≫ (FC.fil (s + r) (k - 1)).arrow := by
      rw [← FC.filDiff_comp_arrow, ← Category.assoc, hd₀]
      simp only [Category.assoc, Subobject.ofLE_arrow]
    have hvariation : (xl - x₀) ≫ (FC.fil s k).arrow ≫ FC.d k =
        c ≫ (FC.fil (s + r) (k - 1)).arrow := by
      have hvambient : (xl - x₀) ≫ (FC.fil s k).arrow ≫ FC.d k =
          v ≫ (FC.fil (s + 1) k).arrow ≫ FC.d k := by
        simpa only [Category.assoc] using
          congrArg (fun f => f ≫ FC.d k) hvembed.symm
      rw [hvambient]
      change v ≫ (FC.fil (s + 1) k).arrow ≫ FC.d k =
        (cdeep ≫ ideep) ≫ (FC.fil (s + r) (k - 1)).arrow
      rw [Category.assoc, Subobject.ofLE_arrow]
      exact ((FC.fil (s + r + 1) (k - 1)).factorThru_arrow _ htarget).symm
    rw [← hreference, ← hvariation, Preadditive.sub_comp]
    abel
  refine ⟨yl, hdiff, ?_⟩
  change yl ≫ FC.filToAssocGraded (s + r) (k - 1) = y
  have hcZero : c ≫ FC.filToAssocGraded (s + r) (k - 1) = 0 := by
    have hz : ideep ≫ FC.filToAssocGraded (s + r) (k - 1) = 0 := by
      dsimp only [ideep, FilteredComplex.filToAssocGraded]
      exact cokernel.condition _
    dsimp only [c]
    simpa only [Category.assoc, comp_zero] using
      congrArg (fun f => cdeep ≫ f) hz
  change y₀ ≫ FC.filToAssocGraded (s + r) (k - 1) = y at _hy₀
  dsimp only [yl]
  rw [Preadditive.add_comp, _hy₀, hcZero, add_zero]

/-- 范围一致检测排除范围内的 crossing。若存在 crossing，先换成
本质 crossing，再把其高过滤源代表元加到原代表元上。新代表元
的像仍落入 `F^p`，但其领先目标不可能仍是 `y`，与一致检测矛盾。 -/
theorem UniformDetection.noGeneralCrossingRange
    (FC : FilteredComplex C) (bnd : FC.IsBounded)
    (r : ℤ) (hr : 0 ≤ r) (s k p : ℤ) {T : C} [Projective T]
    {x : T ⟶ FC.assocGraded s k}
    {y : T ⟶ FC.assocGraded (s + r) (k - 1)}
    (hrel : DifferentialRelation (FC.toSpectralSequence bnd) r (s, k) x y)
    (hdetect : UniformDetection FC bnd r hr s k p hrel) :
    FC.NoGeneralCrossingRange bnd r s k p hrel := by
  classical
  rw [FC.noGeneralCrossingRange_iff_noEssential bnd r s k p hrel]
  rintro ⟨u, m, xu, yu, hsu, hess, hpq, hqr⟩
  let q : ℤ := u + m
  obtain ⟨x₀, y₀, hx₀, hy₀, hd₀⟩ :=
    FC.lift_of_differentialRelation bnd r hr s k hrel
  obtain ⟨x₁, y₁, hx₁, hy₁, hd₁⟩ :=
    FC.lift_of_differentialRelation bnd (m : ℤ) (by omega) u k hess.1
  let ius := Subobject.ofLE (FC.fil u k) (FC.fil s k)
    (FC.fil_anti_of_le k (le_of_lt hsu))
  let xl := x₀ + x₁ ≫ ius
  have hzeroSource : (x₁ ≫ ius) ≫ FC.filToAssocGraded s k = 0 := by
    let iu1 := Subobject.ofLE (FC.fil u k) (FC.fil (s + 1) k)
      (FC.fil_anti_of_le k (by omega))
    let i1s := Subobject.ofLE (FC.fil (s + 1) k) (FC.fil s k)
      (FC.fil_anti s k)
    have hi : ius = iu1 ≫ i1s := by
      apply (cancel_mono (FC.fil s k).arrow).mp
      simp only [ius, iu1, i1s, Category.assoc, Subobject.ofLE_arrow]
    rw [hi]
    have hz : i1s ≫ FC.filToAssocGraded s k = 0 := by
      dsimp only [i1s, FilteredComplex.filToAssocGraded]
      exact cokernel.condition _
    simpa only [Category.assoc, comp_zero] using
      congrArg (fun f => (x₁ ≫ iu1) ≫ f) hz
  have hxl : FC.IsLift s k xl x := by
    change x₀ ≫ FC.filToAssocGraded s k = x at hx₀
    change xl ≫ FC.filToAssocGraded s k = x
    dsimp only [xl]
    rw [Preadditive.add_comp, hx₀, hzeroSource, add_zero]
  have hd₀Ambient : x₀ ≫ (FC.fil s k).arrow ≫ FC.d k =
      y₀ ≫ (FC.fil (s + r) (k - 1)).arrow := by
    rw [← FC.filDiff_comp_arrow, ← Category.assoc, hd₀]
    simp only [Category.assoc, Subobject.ofLE_arrow]
  have hd₁Ambient : x₁ ≫ (FC.fil u k).arrow ≫ FC.d k =
      y₁ ≫ (FC.fil q (k - 1)).arrow := by
    dsimp only [q]
    rw [← FC.filDiff_comp_arrow, ← Category.assoc, hd₁]
    simp only [Category.assoc, Subobject.ofLE_arrow]
  have hxlAmbient : xl ≫ (FC.fil s k).arrow ≫ FC.d k =
      y₀ ≫ (FC.fil (s + r) (k - 1)).arrow +
        y₁ ≫ (FC.fil q (k - 1)).arrow := by
    have hius : ius ≫ (FC.fil s k).arrow = (FC.fil u k).arrow :=
      Subobject.ofLE_arrow _
    have hd₁Embedded : ((x₁ ≫ ius) ≫ (FC.fil s k).arrow) ≫ FC.d k =
        y₁ ≫ (FC.fil q (k - 1)).arrow := by
      have hembed : (x₁ ≫ ius) ≫ (FC.fil s k).arrow =
          x₁ ≫ (FC.fil u k).arrow := by
        calc
          (x₁ ≫ ius) ≫ (FC.fil s k).arrow =
              x₁ ≫ (ius ≫ (FC.fil s k).arrow) := Category.assoc _ _ _
          _ = x₁ ≫ (FC.fil u k).arrow :=
            congrArg (fun f => x₁ ≫ f) hius
      have hd₁Ambient' : (x₁ ≫ (FC.fil u k).arrow) ≫ FC.d k =
          y₁ ≫ (FC.fil q (k - 1)).arrow := by
        simpa only [Category.assoc] using hd₁Ambient
      exact (congrArg (fun f => f ≫ FC.d k) hembed).trans hd₁Ambient'
    have hd₁Embedded' : (x₁ ≫ ius) ≫
        ((FC.fil s k).arrow ≫ FC.d k) =
        y₁ ≫ (FC.fil q (k - 1)).arrow := by
      simpa only [Category.assoc] using hd₁Embedded
    dsimp only [xl]
    rw [Preadditive.add_comp, hd₀Ambient, hd₁Embedded']
  have hp0 : (FC.fil p (k - 1)).Factors
      (y₀ ≫ (FC.fil (s + r) (k - 1)).arrow) := by
    apply Subobject.factors_of_le _
      (FC.fil_anti_of_le (k - 1) (show p ≤ s + r by omega))
    exact Subobject.factors_comp_arrow y₀
  have hp1 : (FC.fil p (k - 1)).Factors
      (y₁ ≫ (FC.fil q (k - 1)).arrow) := by
    apply Subobject.factors_of_le _ (FC.fil_anti_of_le (k - 1) hpq)
    exact Subobject.factors_comp_arrow y₁
  have hxp : (FC.fil p (k - 1)).Factors
      (xl ≫ (FC.fil s k).arrow ≫ FC.d k) := by
    rw [hxlAmbient]
    exact Subobject.factors_add _ _ hp0 hp1
  obtain ⟨yl, hdyl, hyl⟩ := hdetect xl hxl hxp
  have hdylAmbient : xl ≫ (FC.fil s k).arrow ≫ FC.d k =
      yl ≫ (FC.fil (s + r) (k - 1)).arrow := by
    rw [← FC.filDiff_comp_arrow, ← Category.assoc, hdyl]
    simp only [Category.assoc, Subobject.ofLE_arrow]
  have hy₁Ambient : y₁ ≫ (FC.fil q (k - 1)).arrow =
      (yl - y₀) ≫ (FC.fil (s + r) (k - 1)).arrow := by
    rw [Preadditive.sub_comp]
    rw [← hdylAmbient, hxlAmbient]
    abel
  have hy₁zero : y₁ ≫ FC.filToAssocGraded q (k - 1) = 0 := by
    have hdeep : (FC.fil (s + r + 1) (k - 1)).Factors
        ((yl - y₀) ≫ (FC.fil (s + r) (k - 1)).arrow) :=
      FC.isLift_sub_factors (s + r) (k - 1) hyl hy₀
    have hfac : (FC.fil (q + 1) (k - 1)).Factors
        (y₁ ≫ (FC.fil q (k - 1)).arrow) := by
      rw [hy₁Ambient]
      apply Subobject.factors_of_le _
        (FC.fil_anti_of_le (k - 1)
          (show q + 1 ≤ s + r + 1 by omega))
      exact hdeep
    let c := (FC.fil (q + 1) (k - 1)).factorThru
      (y₁ ≫ (FC.fil q (k - 1)).arrow) hfac
    have hc : c ≫ Subobject.ofLE (FC.fil (q + 1) (k - 1))
        (FC.fil q (k - 1)) (FC.fil_anti q (k - 1)) = y₁ := by
      apply (cancel_mono (FC.fil q (k - 1)).arrow).mp
      rw [Category.assoc, Subobject.ofLE_arrow]
      exact (FC.fil (q + 1) (k - 1)).factorThru_arrow _ hfac
    rw [← hc]
    have hz : Subobject.ofLE (FC.fil (q + 1) (k - 1))
        (FC.fil q (k - 1)) (FC.fil_anti q (k - 1)) ≫
        FC.filToAssocGraded q (k - 1) = 0 := by
      dsimp only [FilteredComplex.filToAssocGraded]
      exact cokernel.condition _
    simpa only [Category.assoc, comp_zero] using
      congrArg (fun f => c ≫ f) hz
  have hyuZero : yu = 0 := by
    change y₁ ≫ FC.filToAssocGraded q (k - 1) = yu at hy₁
    exact hy₁.symm.trans hy₁zero
  apply hess.2
  rw [hyuZero]
  exact Subobject.factors_zero

/-- 在目标范围非空时，范围内没有一般 crossing 当且仅当每个满足
`F^p` 条件的源代表元都能检测同一个目标类。 -/
theorem FilteredComplex.noGeneralCrossingRange_iff_uniformDetection
    (FC : FilteredComplex C) (bnd : FC.IsBounded)
    (r : ℤ) (hr : 0 ≤ r) (s k p : ℤ) (hp : p ≤ s + r)
    {T : C} [Projective T]
    {x : T ⟶ FC.assocGraded s k}
    {y : T ⟶ FC.assocGraded (s + r) (k - 1)}
    (hrel : DifferentialRelation (FC.toSpectralSequence bnd) r (s, k) x y) :
    FC.NoGeneralCrossingRange bnd r s k p hrel ↔
      UniformDetection FC bnd r hr s k p hrel := by
  constructor
  · intro hno
    exact hno.uniformDetection FC bnd r hr s k p hp hrel
  · intro hdetect
    exact hdetect.noGeneralCrossingRange FC bnd r hr s k p hrel

/-- 不指定额外下界时，“无 crossing”表示在源过滤的下一层 `s+1`
以上没有一般 crossing。 -/
abbrev FilteredComplex.NoGeneralCrossing
    (FC : FilteredComplex C) (bnd : FC.IsBounded)
    (r s k : ℤ) {T : C} [Projective T]
    {x : T ⟶ FC.assocGraded s k}
    {y : T ⟶ FC.assocGraded (s + r) (k - 1)}
    (hrel : DifferentialRelation (FC.toSpectralSequence bnd) r (s, k) x y) : Prop :=
  FC.NoGeneralCrossingRange bnd r s k (s + 1) hrel

/-- 对正长度关系，普通无 crossing 等价于对 `F^(s+1)` 条件的所有代表元
进行一致检测。这是范围版等价在通常下界处的直接特化。 -/
theorem FilteredComplex.noGeneralCrossing_iff_uniformDetection
    (FC : FilteredComplex C) (bnd : FC.IsBounded)
    (r : ℤ) (hr : 1 ≤ r) (s k : ℤ) {T : C} [Projective T]
    {x : T ⟶ FC.assocGraded s k}
    {y : T ⟶ FC.assocGraded (s + r) (k - 1)}
    (hrel : DifferentialRelation (FC.toSpectralSequence bnd) r (s, k) x y) :
    FC.NoGeneralCrossing bnd r s k hrel ↔
      UniformDetection FC bnd r (by omega) s k (s + 1) hrel :=
  FC.noGeneralCrossingRange_iff_uniformDetection bnd r (by omega)
    s k (s + 1) (by omega) hrel

/-- 每个一般 crossing 都包含一个目标不变的本质 crossing。若原见证已经
本质则直接使用；否则其非零目标属于有限边缘层，
`essential_ancestor_of_nonzero_boundary` 给出来自更高源过滤的本质祖先。 -/
theorem FilteredComplex.generalCrossing_to_essential
    (FC : FilteredComplex C) (bnd : FC.IsBounded)
    (r s k : ℤ) {T : C} [Projective T]
    {x : T ⟶ FC.assocGraded s k}
    {y : T ⟶ FC.assocGraded (s + r) (k - 1)}
    (h : DifferentialRelation (FC.toSpectralSequence bnd) r (s, k) x y)
    (hc : FC.GeneralCrossing bnd r s k h) :
    RelationCrossedBy (FC.toSpectralSequence bnd) Prod.fst
      r (s, k) x y h := by
  classical
  obtain ⟨u, m, x', y', hu, hess, _hlower, hupper⟩ :=
    FC.generalCrossingRange_to_essential bnd r s k (s + 1) h hc
  refine ⟨u - s, by omega, m, (u, k), x', y', by omega, hess, ?_⟩
  change u + (m : ℤ) ≤ s + r
  exact hupper

/-! ## 两项复形 ESS 的循环与边缘 -/

private theorem imageSubobject_eq_top_of_zero_comp_epi_blueprint
    {X Y Z : C} (g : X ⟶ Y) [Epi g] :
    imageSubobject ((kernelSubobject (0 : X ⟶ Z)).arrow ≫ g) = ⊤ := by
  haveI : IsIso (kernelSubobject (0 : X ⟶ Z)).arrow :=
    isIso_kernelSubobject_zero_arrow
  have : Epi ((kernelSubobject (0 : X ⟶ Z)).arrow ≫ g) := epi_comp _ _
  have : Epi (imageSubobject
      ((kernelSubobject (0 : X ⟶ Z)).arrow ≫ g)).arrow :=
    epi_of_epi_fac (imageSubobject_arrow_comp _)
  haveI : IsIso (imageSubobject
      ((kernelSubobject (0 : X ⟶ Z)).arrow ≫ g)).arrow :=
    isIso_of_mono_of_epi _
  exact Subobject.eq_top_of_isIso_arrow _

private theorem imageSubobject_ofLE_bot_comp_eq_bot_blueprint
    {X : C} (a : Subobject X) {Y : C}
    (g : Subobject.underlying.obj a ⟶ Y) :
    imageSubobject (Subobject.ofLE ⊥ a bot_le ≫ g) = ⊥ := by
  have hzero : Subobject.ofLE (⊥ : Subobject X) a bot_le = 0 := by
    have h := Subobject.ofLE_arrow (X := (⊥ : Subobject X))
      (Y := a) bot_le
    rw [Subobject.bot_arrow] at h
    exact (cancel_mono a.arrow).mp (by simp [h])
  simp [hzero, zero_comp, imageSubobject_zero]

/-- 两项复形在复形次数 `1` 没有入射微分，因此任意页的源端边缘子对象
都是零。 -/
theorem BoundedExtensionSS.source_boundary_eq_bot
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι] {ω : Type w}
    {E₁ E₂ : SpectralSequence C ι}
    {A₁ A₂ : ω → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    {bnd₁ : F₁.IsBounded} {bnd₂ : F₂.IsBounded}
    (ext : BoundedExtensionSS conv₁ conv₂ cm bnd₁ bnd₂)
    (t : ω) (s : ℤ) (r : WithTop ℕ) :
    ((ext.ess t).ssData (s, 1)).B r = ⊥ := by
  let FC := ext.complex t
  change FC.boundarySubobject s 1 r = ⊥
  have hd : FC.dToK 1 = 0 := by
    simp [FC, FilteredComplex.dToK, BoundedExtensionSS.complex,
      underlyingComplex, twoTermDiff] <;> rfl
  delta FilteredComplex.boundarySubobject
  cases r with
  | top =>
      dsimp only
      have hI : imageSubobject (FC.dToK 1) ⊓ FC.fil s 1 = ⊥ := by
        rw [hd, imageSubobject_zero, bot_inf_eq]
      convert imageSubobject_ofLE_bot_comp_eq_bot_blueprint
        (FC.fil s 1) (FC.filToAssocGraded s 1) <;>
        first | rfl | simpa using hI
  | coe n =>
      dsimp only
      let d2 : FC.A 2 ⟶ FC.A 1 :=
        eqToHom (congrArg FC.A (show (2 : ℤ) = 1 + 1 by omega)) ≫ FC.dToK 1
      have hd2 : d2 = 0 := by
        dsimp only [d2]
        rw [hd, comp_zero]
      have hI : imageSubobject
          ((FC.fil (s - ↑n + 1) 2).arrow ≫ d2) ⊓ FC.fil s 1 = ⊥ := by
        rw [hd2, comp_zero, imageSubobject_zero, bot_inf_eq]
      convert imageSubobject_ofLE_bot_comp_eq_bot_blueprint
        (FC.fil s 1) (FC.filToAssocGraded s 1) <;>
        first | rfl | simpa [d2] using hI

/-- 两项复形在复形次数 `0` 没有出射微分，因此任意页的目标端循环子对象
都是整个环境对象。 -/
theorem BoundedExtensionSS.target_cycle_eq_top
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι] {ω : Type w}
    {E₁ E₂ : SpectralSequence C ι}
    {A₁ A₂ : ω → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    {bnd₁ : F₁.IsBounded} {bnd₂ : F₂.IsBounded}
    (ext : BoundedExtensionSS conv₁ conv₂ cm bnd₁ bnd₂)
    (t : ω) (s : ℤ) (r : WithTop ℕ) :
    ((ext.ess t).ssData (s, 0)).Z r = ⊤ := by
  let FC := ext.complex t
  change FC.cycleSubobject s 0 r = ⊤
  have hd : FC.d 0 = 0 := by
    simp [FC, BoundedExtensionSS.complex, underlyingComplex, twoTermDiff] <;> rfl
  delta FilteredComplex.cycleSubobject
  cases r with
  | top =>
      dsimp only
      convert imageSubobject_eq_top_of_zero_comp_epi_blueprint
        (Z := FC.A (0 - 1))
        (cokernel.π (Subobject.ofLE (FC.fil (s + 1) 0) (FC.fil s 0)
          (FC.fil_anti s 0))) <;>
        first | rfl | simp only [hd, Category.assoc, comp_zero, zero_comp]
  | coe n =>
      dsimp only
      convert imageSubobject_eq_top_of_zero_comp_epi_blueprint
        (Z := cokernel (FC.fil (s + ↑n) (0 - 1)).arrow)
        (cokernel.π (Subobject.ofLE (FC.fil (s + 1) 0) (FC.fil s 0)
          (FC.fil_anti s 0))) <;>
        first | rfl | simp only [hd, Category.assoc, comp_zero, zero_comp]

/-- 环境对象按第 `r` 层边缘取商。 -/
noncomputable def SSData.boundaryQuotient (D : SSData C)
    (r : WithTop ℕ) : C :=
  cokernel (D.B r).arrow

/-- 若第 `r` 层边缘为零，则该页规范同构于循环子对象。 -/
noncomputable def SSData.pageIsoCycleObjectOfBoundaryEqBot
    (D : SSData C) (r : WithTop ℕ) (hB : D.B r = ⊥) :
    D.page r ≅ Subobject.underlying.obj (D.Z r) := by
  let i := Subobject.ofLE (D.B r) (D.Z r) (D.B_le_Z r)
  have hi : i = 0 := by
    apply (cancel_mono (D.Z r).arrow).mp
    rw [Subobject.ofLE_arrow]
    change (D.B r).arrow = 0 ≫ (D.Z r).arrow
    rw [zero_comp, hB, Subobject.bot_arrow]
  exact cokernelIsoOfEq hi ≪≫ cokernelZeroIsoTarget

/-- 若第 `r` 层循环为整个环境对象，则该页规范同构于环境对象模边缘。 -/
noncomputable def SSData.pageIsoBoundaryQuotientOfCycleEqTop
    (D : SSData C) (r : WithTop ℕ) (hZ : D.Z r = ⊤) :
    D.page r ≅ D.boundaryQuotient r := by
  let i := Subobject.ofLE (D.B r) (D.Z r) (D.B_le_Z r)
  letI : IsIso (D.Z r).arrow :=
    (Subobject.isIso_arrow_iff_eq_top (D.Z r)).2 hZ
  exact (cokernelCompIsIso i (D.Z r).arrow).symm ≪≫
    cokernelIsoOfEq (Subobject.ofLE_arrow (D.B_le_Z r))

/-- 两项复形 ESS 的第 `r` 页分解：次数 `1` 的分量是源端循环对象，
次数 `0` 的分量是目标环境对象模边缘。这里的二元直和正是 Blueprint
公式中被合写为 `Z ⊕ E∞/B` 的两个复形次数。 -/
noncomputable def BoundedExtensionSS.pageDecompositionIso
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι] {ω : Type w}
    {E₁ E₂ : SpectralSequence C ι}
    {A₁ A₂ : ω → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    {bnd₁ : F₁.IsBounded} {bnd₂ : F₂.IsBounded}
    (ext : BoundedExtensionSS conv₁ conv₂ cm bnd₁ bnd₂)
    (t : ω) (s : ℤ) (r : WithTop ℕ) :
    (((ext.ess t).ssData (s, 1)).page r ⊞
        ((ext.ess t).ssData (s, 0)).page r) ≅
      (Subobject.underlying.obj (((ext.ess t).ssData (s, 1)).Z r) ⊞
        ((ext.ess t).ssData (s, 0)).boundaryQuotient r) :=
  biprod.mapIso
    (((ext.ess t).ssData (s, 1)).pageIsoCycleObjectOfBoundaryEqBot r
      (ext.source_boundary_eq_bot t s r))
    (((ext.ess t).ssData (s, 0)).pageIsoBoundaryQuotientOfCycleEqTop r
      (ext.target_cycle_eq_top t s r))

/-! ## 收敛与检测的统一见证 -/

/-- Blueprint 使用的收敛和检测数据。`convergence` 给出
`E∞ ≅ gr A`，而 `Detects convergence` 给出元素级检测关系；其余三个字段
明确记录过滤的穷尽、Hausdorff 与完备条件。 -/
structure ConvergenceDetectionWitness
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {ω : Type w} (E : SpectralSequence C ι) (A : ω → C)
    (F : Filtration A) : Type max u v w where
  convergence : Convergence E A F
  exhaustive : F.IsExhaustive
  hausdorff : F.IsHausdorff
  complete : F.IsComplete

/-! ## 交换方块诱导的 ESS 自然性 -/

variable [LocallySmall.{u} C] [WellPowered.{u} C]
variable [HasWidePullbacks.{u} C] [HasCoproducts.{u} C]

/-- 收敛谱序列交换方块在每个 abutment 次数上给出两个两项过滤复形之间
的态射：次数 `1` 取左边 `p`，次数 `0` 取右边 `q`。链映射条件正是
`q f = g p`，过滤相容性分别来自 `p` 与 `q`。 -/
noncomputable def HomotopyCommSquare.essFilteredComplexMorphism
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι] {ω : Type w}
    {E₁ E₂ E₃ E₄ : SpectralSequence C ι}
    {A₁ A₂ A₃ A₄ : ω → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {F₃ : Filtration A₃} {F₄ : Filtration A₄}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {conv₃ : Convergence E₃ A₃ F₃} {conv₄ : Convergence E₄ A₄ F₄}
    (sq : HomotopyCommSquare conv₁ conv₂ conv₃ conv₄) (t : ω) :
    FilteredComplexMorphism (sq.extf.complex t) (sq.extg.complex t) :=
  underlyingComplexMorphism
    sq.cmf.aMap sq.cmf.filtration_compat
    sq.cmg.aMap sq.cmg.filtration_compat
    sq.cmp.aMap sq.cmq.aMap (fun t => (sq.abutment_comm t).symm)
    sq.cmp.filtration_compat sq.cmq.filtration_compat t

/-- 上一态射的有界过滤复形版本。 -/
noncomputable def HomotopyCommSquare.essBoundedMorphism
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι] {ω : Type w}
    {E₁ E₂ E₃ E₄ : SpectralSequence C ι}
    {A₁ A₂ A₃ A₄ : ω → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {F₃ : Filtration A₃} {F₄ : Filtration A₄}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {conv₃ : Convergence E₃ A₃ F₃} {conv₄ : Convergence E₄ A₄ F₄}
    (sq : HomotopyCommSquare conv₁ conv₂ conv₃ conv₄) (t : ω) :
    (⟨sq.extf.complex t, sq.extf.bounded t⟩ : BoundedFilteredComplex C) ⟶
      (⟨sq.extg.complex t, sq.extg.bounded t⟩ : BoundedFilteredComplex C) :=
  sq.essFilteredComplexMorphism t

/-- 交换方块无条件诱导从 `f`-ESS 到 `g`-ESS 的谱序列态射。该态射在
每一页都与微分交换；它是稳定页推论所需的未移位自然性基础。 -/
private noncomputable def HomotopyCommSquare.essSpectralSequenceMorphismRaw
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι] {ω : Type w}
    {E₁ E₂ E₃ E₄ : SpectralSequence C ι}
    {A₁ A₂ A₃ A₄ : ω → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {F₃ : Filtration A₃} {F₄ : Filtration A₄}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {conv₃ : Convergence E₃ A₃ F₃} {conv₄ : Convergence E₄ A₄ F₄}
    (sq : HomotopyCommSquare conv₁ conv₂ conv₃ conv₄) (t : ω) :
    (⟨sq.extf.complex t, sq.extf.bounded t⟩ : BoundedFilteredComplex C).FC.toSpectralSequence
        (⟨sq.extf.complex t, sq.extf.bounded t⟩ : BoundedFilteredComplex C).bnd ⟶
      (⟨sq.extg.complex t, sq.extg.bounded t⟩ : BoundedFilteredComplex C).FC.toSpectralSequence
        (⟨sq.extg.complex t, sq.extg.bounded t⟩ : BoundedFilteredComplex C).bnd :=
  FilteredComplexMorphism.toSpectralSequenceMorphism
    (sq.essBoundedMorphism t)

/-- `essSpectralSequenceMorphismRaw` 按 `BoundedExtensionSS.ess` 的名称重写
后的公开版本。 -/
noncomputable def HomotopyCommSquare.essSpectralSequenceMorphism
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι] {ω : Type w}
    {E₁ E₂ E₃ E₄ : SpectralSequence C ι}
    {A₁ A₂ A₃ A₄ : ω → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {F₃ : Filtration A₃} {F₄ : Filtration A₄}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {conv₃ : Convergence E₃ A₃ F₃} {conv₄ : Convergence E₄ A₄ F₄}
    (sq : HomotopyCommSquare conv₁ conv₂ conv₃ conv₄) (t : ω) :
    sq.extf.ess t ⟶ sq.extg.ess t := by
  change
    (sq.extf.complex t).toSpectralSequence (sq.extf.bounded t) ⟶
      (sq.extg.complex t).toSpectralSequence (sq.extg.bounded t)
  exact sq.essSpectralSequenceMorphismRaw t

/-- 交换方块诱导的 ESS 页映射与每一页微分交换。 -/
theorem HomotopyCommSquare.essPageMap_comm
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι] {ω : Type w}
    {E₁ E₂ E₃ E₄ : SpectralSequence C ι}
    {A₁ A₂ A₃ A₄ : ω → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {F₃ : Filtration A₃} {F₄ : Filtration A₄}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {conv₃ : Convergence E₃ A₃ F₃} {conv₄ : Convergence E₄ A₄ F₄}
    (sq : HomotopyCommSquare conv₁ conv₂ conv₃ conv₄)
    (t : ω) (r : ℤ) (k : ℤ × ℤ) :
    let E := sq.extf.ess t
    let E' := sq.extg.ess t
    let F := sq.essSpectralSequenceMorphism t
    let n : WithTop ℕ := ↑(r - E.r₀).toNat
    let n' : WithTop ℕ := ↑(r - E'.r₀).toNat
    let hn : n = n' := congrArg
      (fun r₀ => (↑(r - r₀).toNat : WithTop ℕ)) F.r₀_eq
    let hk : k + E.diffDeg r = k + E'.diffDeg r :=
      congrArg (fun d => k + d) (congrFun F.diffDeg_eq r)
    let sourceMap := F.pageMapOfEq k k rfl n n' hn
    let targetMap := F.pageMapOfEq
      (k + E.diffDeg r) (k + E'.diffDeg r) hk n n' hn
    sourceMap ≫ E'.d r k = E.d r k ≫ targetMap := by
  exact (sq.essSpectralSequenceMorphism t).comm_d r k

/-! ## 零复合与永久循环 -/

/-- 若两个可复合的收敛谱序列态射在固定 abutment 次数上的复合为零，
则任意由第一条边的无界 ESS 微分命中的目标，都给出第二条边的相容永久
循环。这里“永久”使用 `ESSPermanentCycle` 的代表元定义，因此结论足以和
真正 Hausdorff 条件以及 abutment 正合性定理组合。 -/
theorem essPermanentCycle_of_zero_composite
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι] {ω : Type w}
    (V₁ V₂ V₃ : ConvergingSS C ι ω)
    (f : V₁ ⟶ V₂) (g : V₂ ⟶ V₃) (t : ω)
    (u r : ℤ) (hr : 0 ≤ r) {T : C} [Projective T]
    (x : T ⟶ (V₁.E.ssData (V₁.conv.reindexEquiv.symm (u, t))).eInfty)
    (y : T ⟶ (V₂.E.ssData (V₂.conv.reindexEquiv.symm (u + r, t))).eInfty)
    (hrel : DifferentialRelation (ExtensionSpectralSequence f t) r (u, 1) x
      (Eq.mpr (congrArg (fun X : C => T ⟶ X)
        (show ((ExtensionSpectralSequence f t).ssData
            ((u, 1) + (ExtensionSpectralSequence f t).diffDeg r)).V =
          (unboundedExtensionSSData f t (u + r, 0)).V by
            rw [ExtensionSpectralSequence_diffDeg]
            simp only [Prod.mk_add_mk]
            rfl)) y))
    (hzero : f.aMap t ≫ g.aMap t = 0) :
    ESSPermanentCycle g t (u + r) y := by
  classical
  obtain ⟨xl, yl, _hxl, hyl, hd⟩ :=
    unbounded_lift_of_differentialRelation f t r hr u 1 hrel
  have hylF : UnboundedExtensionIsLift f t (u + r) 0 yl y := by
    simpa [ExtensionSpectralSequence_diffDeg] using hyl
  have hylG : UnboundedExtensionIsLift g t (u + r) 1 yl y :=
    unboundedExtensionIsLift_target_source f g t (u + r) yl y hylF
  refine ⟨yl, hylG, ?_⟩
  intro q
  have hambient := unbounded_lift_ambient_map f t u (u + r) (by omega) xl yl hd
  have hambient' :
      xl ≫ (V₁.F.F u t).arrow ≫ f.aMap t =
        yl ≫ (V₂.F.F (u + r) t).arrow := by
    simpa [unboundedUnderlyingComplex, underlyingComplex, twoTermFil, twoTermObj]
      using hambient
  have hyzero : (yl ≫ (V₂.F.F (u + r) t).arrow) ≫ g.aMap t = 0 := by
    calc
      (yl ≫ (V₂.F.F (u + r) t).arrow) ≫ g.aMap t =
          (xl ≫ (V₁.F.F u t).arrow ≫ f.aMap t) ≫ g.aMap t := by
            rw [hambient']
      _ = xl ≫ (V₁.F.F u t).arrow ≫ (f.aMap t ≫ g.aMap t) := by
            simp only [Category.assoc]
      _ = 0 := by rw [hzero, comp_zero, comp_zero]
  change (V₃.F.F q t).Factors
    ((yl ≫ (V₂.F.F (u + r) t).arrow) ≫ g.aMap t)
  rw [hyzero]
  exact (Subobject.factors_iff _ _).2 ⟨0, zero_comp⟩

end KIPBase.SpectralSequence
