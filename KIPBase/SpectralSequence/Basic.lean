/-
  KIPBase.SpectralSequence.Basic
  §1.1 嵌套子空间（循环/边缘）方法的谱序列

  核心数据是 `SSData`，它打包单个双次数上的经典嵌套包含链
    V ⊇ Z 0 ⊇ Z 1 ⊇ ... ⊇ Z ⊤ ⊇ B ⊤ ⊇ ... ⊇ B 1 ⊇ B 0
  其中 E_r = Z r / B r。

  `SpectralSequence` 随后把所有双次数上的 SSData 与连接不同双次数
  分量的微分组装在一起。页对象 `Page r k` 由 `SSData` 派生，
  不单独存储。
-/
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.CategoryTheory.Abelian.Subobject
import Mathlib.CategoryTheory.Abelian.Pseudoelements
import Mathlib.Tactic.Abel

namespace KIPBase.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v w

set_option linter.dupNamespace false

/-! ### SSData：单个双次数上的嵌套子空间数据 -/

/-- 谱序列在单个双次数上的嵌套子空间数据。
  `Z r` 是 r-循环（随 r 递减），`B r` 是 r-边缘（随 r 递增），
  二者都是环境对象 `V` 的子对象。
  用 `WithTop ℕ` 索引，`⊤` 表示 ∞ 层。 -/
structure SSData (C : Type u) [Category.{v} C] [Abelian C] where
  /-- 环境对象（例如链复形的一个分次分量） -/
  V : C
  /-- V 的 r-循环子对象，递减：Z 0 ⊇ Z 1 ⊇ ... ⊇ Z ⊤ -/
  Z : WithTop ℕ → Subobject V
  /-- V 的 r-边缘子对象，递增：B 0 ⊆ B 1 ⊆ ... ⊆ B ⊤ -/
  B : WithTop ℕ → Subobject V
  /-- Z 反单调：页指标越大循环子对象越小 -/
  Z_anti : Antitone Z
  /-- B 单调：页指标越大边缘子对象越大 -/
  B_mono : Monotone B
  /-- 一切都是 0-循环：Z 0 是整个环境对象 -/
  Z_zero : Z 0 = ⊤
  /-- 每一层上边缘总包含在循环里 -/
  B_le_Z : ∀ r, B r ≤ Z r
  /-- Z ⊤ 是所有有限 Z_i 的最大下界。
      与 `Z_anti`（给出对所有 i 有 `Z ⊤ ≤ Z ↑i`）合起来，
      即 `Z ⊤ = ⨅ᵢ Z ↑i`。 -/
  Z_top_greatest : ∀ (X : Subobject V), (∀ i : ℕ, X ≤ Z ↑i) → X ≤ Z ⊤
  /-- B ⊤ 是所有有限 B_i 的最小上界。
      与 `B_mono`（给出对所有 i 有 `B ↑i ≤ B ⊤`）合起来，
      即 `B ⊤ = ⨆ᵢ B ↑i`。 -/
  B_top_least : ∀ (X : Subobject V), (∀ i : ℕ, B ↑i ≤ X) → B ⊤ ≤ X

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- 该双次数上的第 r 页：E_r = Z r / B r = cokernel(B r ↪ Z r)。 -/
@[reducible] noncomputable def SSData.page (D : SSData C) (r : WithTop ℕ) : C :=
  cokernel (Subobject.ofLE (D.B r) (D.Z r) (D.B_le_Z r))

/-- 该双次数上的 E∞ 页：Z ⊤ / B ⊤。 -/
noncomputable def SSData.eInfty (D : SSData C) : C := D.page ⊤

/-- 从 Z r 的底层对象到页 E_r = Z r / B r 的投影。 -/
@[reducible] noncomputable def SSData.pageπ (D : SSData C) (r : WithTop ℕ) :
    Subobject.underlying.obj (D.Z r) ⟶ D.page r :=
  cokernel.π (Subobject.ofLE (D.B r) (D.Z r) (D.B_le_Z r))

theorem SSData.B_bot_le_Z (D : SSData C) (r : WithTop ℕ) : D.B ⊥ ≤ D.Z r :=
  le_trans (D.B_mono bot_le) (D.B_le_Z r)

/-- 当 B r = Z r 时，页 E_r = Z r / B r 为零。
    B r ↪ Z r 在 B r = Z r 时是同构，故为满态射，
    其 cokernel 消失。 -/
theorem SSData.page_isZero_of_eq (D : SSData C) (r : WithTop ℕ) (h : D.B r = D.Z r) :
    IsZero (D.page r) := by
  unfold SSData.page
  have : IsIso (Subobject.ofLE (D.B r) (D.Z r) (D.B_le_Z r)) := by
    rw [← Subobject.isoOfEq_hom _ _ h]
    infer_instance
  exact isZero_cokernel_of_epi _

/-- 反向：若页为零，则 B r = Z r。 -/
theorem SSData.eq_of_page_isZero (D : SSData C) (r : WithTop ℕ) (h : IsZero (D.page r)) :
    D.B r = D.Z r := by
  unfold SSData.page at h
  have hepi : Epi (Subobject.ofLE (D.B r) (D.Z r) (D.B_le_Z r)) := by
    rwa [Preadditive.epi_iff_isZero_cokernel]
  haveI : IsIso (Subobject.ofLE (D.B r) (D.Z r) (D.B_le_Z r)) := isIso_of_mono_of_epi _
  apply le_antisymm (D.B_le_Z r)
  exact Subobject.le_of_comm (inv (Subobject.ofLE (D.B r) (D.Z r) (D.B_le_Z r)))
    (by simp [Subobject.ofLE_arrow])

/-! ### 分次复形 -/

/-- 阿贝尔范畴 `C` 中以 `ι` 索引的分次复形。
    由一个分次对象和一个固定次数的齐次微分组成，满足 d² = 0。 -/
structure GradedComplex (C : Type u) [Category.{v} C] [Abelian C]
    (ι : Type w) [AddCommGroup ι] where
  /-- 分次对象：`obj k` 是指标 k 处的分量。 -/
  obj : ι → C
  /-- 微分的次数。 -/
  d_deg : ι
  /-- 微分：`d k : obj k ⟶ obj (k + d_deg)`。 -/
  d : (k : ι) → obj k ⟶ obj (k + d_deg)
  /-- d² = 0：两个相邻微分的合成为零。 -/
  d_sq : ∀ k, d k ≫ d (k + d_deg) = 0

/-- 分次复形在指标 `k` 处的短复形：
    `obj (k - d_deg) → obj k → obj (k + d_deg)`，零条件来自 d²。
    用 `eqToHom` 处理重指标 `(k - d_deg) + d_deg = k`。 -/
noncomputable def GradedComplex.shortComplex
    {ι : Type w} [AddCommGroup ι]
    (G : GradedComplex C ι) (k : ι) : ShortComplex C :=
  { X₁ := G.obj (k - G.d_deg)
    X₂ := G.obj k
    X₃ := G.obj (k + G.d_deg)
    f := G.d (k - G.d_deg) ≫ eqToHom (show G.obj (k - G.d_deg + G.d_deg) = G.obj k by
      congr 1; abel)
    g := G.d k
    zero := by
      simp only [Category.assoc]
      have key : eqToHom (show G.obj (k - G.d_deg + G.d_deg) = G.obj k by
          congr 1; abel) ≫ G.d k =
        G.d (k - G.d_deg + G.d_deg) ≫ eqToHom (show G.obj (k - G.d_deg + G.d_deg + G.d_deg) =
          G.obj (k + G.d_deg) by congr 1; abel) := by
        rw [eqToHom_comp_iff]; simp
      rw [key, ← Category.assoc, G.d_sq, zero_comp] }

/-- 分次复形在指标 `k` 处的同调。 -/
noncomputable def GradedComplex.homology
    {ι : Type w} [AddCommGroup ι]
    (G : GradedComplex C ι) (k : ι) : C :=
  (G.shortComplex k).homology

/-! ### PreSS：谱序列的纯数据部分 -/

/-- 预谱序列（PreSS）：谱序列的纯数据载体。
  仅包含数据（起始页指标 r₀、每个双次数上的嵌套子空间数据 ssData、
  微分次数函数 diffDeg、微分 d），不含任何证明性条件
  （d∘d = 0、Z_succ、B_succ 等一律剥离）。
  构造谱序列时分两段：先产出 PreSS，证明义务之后逐条补齐。
  页对象不单独存储，仍由 ssData 派生：`(ssData k).page ↑(r - r₀).toNat`。 -/
structure PreSS (C : Type u) [Category.{v} C] [Abelian C]
    (ι : Type w) [AddCommGroup ι] [DecidableEq ι] where
  /-- 起始页指标 -/
  r₀ : ℤ
  /-- 每个双次数上的嵌套子空间数据（V、Z 塔、B 塔） -/
  ssData : ι → SSData C
  /-- 微分 d_r 的次数 -/
  diffDeg : ℤ → ι
  /-- 微分 d_r^k : E_r^k → E_r^{k + diffDeg r}，
      定义域与陪域均由 ssData 派生 -/
  d : (r : ℤ) → (k : ι) →
    ((ssData k).page ↑(r - r₀).toNat ⟶
     (ssData (k + diffDeg r)).page ↑(r - r₀).toNat)

/-- 预谱序列的页对象 `E_r^k`，由嵌套子空间数据派生：
    `(ssData k).page ↑(r - r₀).toNat`。 -/
@[reducible] noncomputable def PreSS.Page
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (E : PreSS C ι) (r : ℤ) (k : ι) : C :=
  (E.ssData k).page ↑(r - E.r₀).toNat

/-! ### PreSS 的态射 -/

/-- underlying 态射（UnderlyingMorphism）：裸的 φ 映射族，
  不带任何条件。它是态射层次的最底层：
  加保 B/Z 条件得 SSDataMorphism，再加保微分条件得 PreSSMorphism。 -/
structure UnderlyingMorphism
    (ι : Type w) [AddCommGroup ι] [DecidableEq ι]
    (D D' : ι → SSData C) where
  /-- 每个双次数上环境对象之间的映射 -/
  φ : ∀ (k : ι), (D k).V ⟶ (D' k).V

/-- SSData 的态射（SSDataMorphism）：underlying morphism 加保 B/Z 条件。
  φ 是每个双次数上环境对象 `V` 之间的映射族；
  preserves_Z / preserves_B 要求 φ 把 Z 塔、B 塔分别映入对方的 Z 塔、B 塔
  （经子对象提升表达）。 -/
structure SSDataMorphism
    (ι : Type w) [AddCommGroup ι] [DecidableEq ι]
    (D D' : ι → SSData C) extends UnderlyingMorphism ι D D' where
  /-- φ 保持 Z_r：把 Z_r(D k) 映入 Z_r(D' k) -/
  preserves_Z : ∀ (k : ι) (r : WithTop ℕ),
    ∃ (lift : Subobject.underlying.obj ((D k).Z r) ⟶
              Subobject.underlying.obj ((D' k).Z r)),
      lift ≫ ((D' k).Z r).arrow = ((D k).Z r).arrow ≫ φ k
  /-- φ 保持 B_r：把 B_r(D k) 映入 B_r(D' k) -/
  preserves_B : ∀ (k : ι) (r : WithTop ℕ),
    ∃ (lift : Subobject.underlying.obj ((D k).B r) ⟶
              Subobject.underlying.obj ((D' k).B r)),
      lift ≫ ((D' k).B r).arrow = ((D k).B r).arrow ≫ φ k

/-- 从 SSDataMorphism 遗忘保 B/Z 条件得到 underlying 态射。 -/
def SSDataMorphism.toUnderlying
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {D D' : ι → SSData C} (f : SSDataMorphism ι D D') :
    UnderlyingMorphism ι D D' where
  φ := f.φ

/-- `SSDataMorphism` 在第 `r` 页诱导的规范态射。

    该映射不是额外选择的页态射：它由 `preserves_B` 与 `preserves_Z`
    给出的提升通过 `cokernel.map` 构造，因此确实是底层映射 `φ` 在商
    `Z r / B r` 上诱导的映射。 -/
noncomputable def SSDataMorphism.pageMap
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {D D' : ι → SSData C} (f : SSDataMorphism ι D D')
    (k : ι) (r : WithTop ℕ) :
    (D k).page r ⟶ (D' k).page r :=
  cokernel.map
    (Subobject.ofLE ((D k).B r) ((D k).Z r) ((D k).B_le_Z r))
    (Subobject.ofLE ((D' k).B r) ((D' k).Z r) ((D' k).B_le_Z r))
    (f.preserves_B k r).choose
    (f.preserves_Z k r).choose
    (by
      have hB := (f.preserves_B k r).choose_spec
      have hZ := (f.preserves_Z k r).choose_spec
      apply (cancel_mono ((D' k).Z r).arrow).mp
      simp only [Category.assoc, hZ, Subobject.ofLE_arrow, hB,
        Subobject.ofLE_arrow_assoc])

/-- 规范页态射与 `Z r → Z r / B r` 的商投影相容。 -/
theorem SSDataMorphism.pageπ_pageMap
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {D D' : ι → SSData C} (f : SSDataMorphism ι D D')
    (k : ι) (r : WithTop ℕ) :
    (D k).pageπ r ≫ f.pageMap k r =
      (f.preserves_Z k r).choose ≫ (D' k).pageπ r := by
  simp [SSDataMorphism.pageMap, SSData.pageπ]

/-- 规范页态射只由底层映射 `φ` 决定，与保 `B/Z` 的存在见证选择无关。 -/
theorem SSDataMorphism.pageMap_eq_of_φ_eq
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {D D' : ι → SSData C} (f g : SSDataMorphism ι D D')
    (k : ι) (r : WithTop ℕ) (hφ : f.φ k = g.φ k) :
    f.pageMap k r = g.pageMap k r := by
  haveI : Epi ((D k).pageπ r) := by
    dsimp only [SSData.pageπ]
    infer_instance
  apply (cancel_epi ((D k).pageπ r)).mp
  rw [f.pageπ_pageMap, g.pageπ_pageMap]
  congr 1
  apply (cancel_mono ((D' k).Z r).arrow).mp
  rw [(f.preserves_Z k r).choose_spec, (g.preserves_Z k r).choose_spec, hφ]

/-- 底层映射为恒等时，规范页态射也是恒等。 -/
theorem SSDataMorphism.pageMap_eq_id
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {D : ι → SSData C} (f : SSDataMorphism ι D D)
    (k : ι) (r : WithTop ℕ) (hφ : f.φ k = 𝟙 _) :
    f.pageMap k r = 𝟙 _ := by
  haveI : Epi ((D k).pageπ r) := by
    dsimp only [SSData.pageπ]
    infer_instance
  apply (cancel_epi ((D k).pageπ r)).mp
  rw [f.pageπ_pageMap, Category.comp_id]
  have hlift : (f.preserves_Z k r).choose = 𝟙 _ := by
    apply (cancel_mono ((D k).Z r).arrow).mp
    rw [(f.preserves_Z k r).choose_spec, hφ]
    simp
  rw [hlift, Category.id_comp]

/-- 底层映射为复合时，规范页态射等于两个规范页态射的复合。 -/
theorem SSDataMorphism.pageMap_eq_comp
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {D₁ D₂ D₃ : ι → SSData C}
    (f : SSDataMorphism ι D₁ D₂) (g : SSDataMorphism ι D₂ D₃)
    (h : SSDataMorphism ι D₁ D₃) (k : ι) (r : WithTop ℕ)
    (hφ : h.φ k = f.φ k ≫ g.φ k) :
    h.pageMap k r = f.pageMap k r ≫ g.pageMap k r := by
  haveI : Epi ((D₁ k).pageπ r) := by
    dsimp only [SSData.pageπ]
    infer_instance
  apply (cancel_epi ((D₁ k).pageπ r)).mp
  rw [h.pageπ_pageMap]
  have hlift : (h.preserves_Z k r).choose =
      (f.preserves_Z k r).choose ≫ (g.preserves_Z k r).choose := by
    apply (cancel_mono ((D₃ k).Z r).arrow).mp
    rw [(h.preserves_Z k r).choose_spec, Category.assoc,
      (g.preserves_Z k r).choose_spec, ← Category.assoc,
      (f.preserves_Z k r).choose_spec, Category.assoc, hφ]
  calc
    (h.preserves_Z k r).choose ≫ (D₃ k).pageπ r =
        ((f.preserves_Z k r).choose ≫ (g.preserves_Z k r).choose) ≫
          (D₃ k).pageπ r := by rw [hlift]
    _ = (f.preserves_Z k r).choose ≫
          ((g.preserves_Z k r).choose ≫ (D₃ k).pageπ r) :=
      Category.assoc _ _ _
    _ = (f.preserves_Z k r).choose ≫
          ((D₂ k).pageπ r ≫ g.pageMap k r) := by
      rw [g.pageπ_pageMap]
    _ = ((f.preserves_Z k r).choose ≫ (D₂ k).pageπ r) ≫
          g.pageMap k r := (Category.assoc _ _ _).symm
    _ = ((D₁ k).pageπ r ≫ f.pageMap k r) ≫ g.pageMap k r := by
      rw [f.pageπ_pageMap]
    _ = (D₁ k).pageπ r ≫ (f.pageMap k r ≫ g.pageMap k r) :=
      Category.assoc _ _ _

/-- 当分次指标和页层指标分别由等式识别时，对规范页态射作相应搬运。
    所有 `PreSS` 页态射都通过这一函数构造，避免把 `eqToHom` 散落在定义中。 -/
noncomputable def SSDataMorphism.pageMapOfEq
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {D D' : ι → SSData C} (f : SSDataMorphism ι D D')
    (k k' : ι) (hk : k = k') (r r' : WithTop ℕ) (hr : r = r') :
    (D k).page r ⟶ (D' k').page r' :=
  f.pageMap k r ≫ eqToHom (by rw [hk, hr])

@[simp]
theorem SSDataMorphism.pageMapOfEq_rfl
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {D D' : ι → SSData C} (f : SSDataMorphism ι D D')
    (k : ι) (r : WithTop ℕ) :
    f.pageMapOfEq k k rfl r r rfl = f.pageMap k r := by
  simp [SSDataMorphism.pageMapOfEq]

/-- 带指标搬运的规范页态射保持复合。 -/
theorem SSDataMorphism.pageMapOfEq_comp
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {D₁ D₂ D₃ : ι → SSData C}
    (f : SSDataMorphism ι D₁ D₂) (g : SSDataMorphism ι D₂ D₃)
    (h : SSDataMorphism ι D₁ D₃)
    (k₁ k₂ k₃ : ι) (hk₁₂ : k₁ = k₂) (hk₂₃ : k₂ = k₃)
    (r₁ r₂ r₃ : WithTop ℕ) (hr₁₂ : r₁ = r₂) (hr₂₃ : r₂ = r₃)
    (hφ : h.φ k₁ = f.φ k₁ ≫ g.φ k₁) :
    h.pageMapOfEq k₁ k₃ (hk₁₂.trans hk₂₃)
        r₁ r₃ (hr₁₂.trans hr₂₃) =
      f.pageMapOfEq k₁ k₂ hk₁₂ r₁ r₂ hr₁₂ ≫
        g.pageMapOfEq k₂ k₃ hk₂₃ r₂ r₃ hr₂₃ := by
  subst k₂
  subst k₃
  subst r₂
  subst r₃
  simp only [SSDataMorphism.pageMapOfEq_rfl]
  exact SSDataMorphism.pageMap_eq_comp f g h k₁ r₁ hφ

/-- 预谱序列的态射（PreSSMorphism）：SSData 的态射加保微分条件。
  `toSSDataMorphism` 把 PreSS 的 ssData 函数送到 SSDataMorphism
  （φ 与 preserves_Z / preserves_B 逐字继承），
  comm_d 要求页上诱导的映射与微分 d_r 交换。
  后续 SpectralSequenceMorphism 可改为 extends PreSSMorphism。 -/
structure PreSSMorphism
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (E E' : PreSS C ι) extends SSDataMorphism ι E.ssData E'.ssData where
  /-- 谱序列态射保持起始页。这个条件保证同一个整数页在源、目标中
      对应同一个 `SSData` 层。 -/
  r₀_eq : E.r₀ = E'.r₀
  /-- 谱序列态射保持微分的次数。 -/
  diffDeg_eq : E.diffDeg = E'.diffDeg
  /-- φ 与微分交换：页上诱导的映射与微分 d_r 交换。 -/
  comm_d : ∀ (r : ℤ) (k : ι),
    let n : WithTop ℕ := ↑(r - E.r₀).toNat
    let n' : WithTop ℕ := ↑(r - E'.r₀).toNat
    let hn : n = n' := congrArg
      (fun r₀ => (↑(r - r₀).toNat : WithTop ℕ)) r₀_eq
    let hk : k + E.diffDeg r = k + E'.diffDeg r :=
      congrArg (fun d => k + d) (congrFun diffDeg_eq r)
    let f_page_k := toSSDataMorphism.pageMapOfEq k k rfl n n' hn
    let f_page_kd := toSSDataMorphism.pageMapOfEq
      (k + E.diffDeg r) (k + E'.diffDeg r) hk n n' hn
    f_page_k ≫ E'.d r k = E.d r k ≫ f_page_kd

/-- 从 PreSSMorphism 遗忘微分交换条件得到 SSDataMorphism。
    因 `PreSSMorphism extends SSDataMorphism`，此即父结构的强制上行转换。 -/
def PreSSMorphism.ssDataMorphism
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {E E' : PreSS C ι} (f : PreSSMorphism E E') :
    SSDataMorphism ι E.ssData E'.ssData where
  φ := f.φ
  preserves_Z := f.preserves_Z
  preserves_B := f.preserves_B

/-! ### 谱序列 -/

/-- 谱序列：数据与证明分离。
  `extends PreSS` 继承纯数据载体（r₀、ssData、diffDeg、d），
  再以等式条件补齐证明义务（d_comp_d、Z_succ、B_succ）；
  原冗余字段 induced_d / induced_d_eq（被钉死等于 pageπ）删除，
  其角色由派生 `SSData.pageπ` 取代。 -/
structure SpectralSequence (C : Type u) [Category.{v} C] [Abelian C]
    (ι : Type w) [AddCommGroup ι] [DecidableEq ι] extends PreSS C ι where
  /-- d_r ∘ d_r = 0（逐分量） -/
  d_comp_d : ∀ (r : ℤ) (k : ι),
    d r k ≫ d r (k + diffDeg r) = 0
  /-- 双次数 k 处 d_r 的核（视为页 E_r^k = Z_n/B_n 的子对象）
      等于 Z_{n+1} → Z_n → Z_n/B_n 的像。
      此处 n = (r - r₀).toNat。
      数学上：k 处 ker(d_r) = E_r^k 内的 Z_{r+1}/B_r。
      只对 r ≥ r₀（页有意义处）陈述。 -/
  Z_succ : ∀ (r : ℤ) (k : ι) (_ : r₀ ≤ r),
    let n := (r - r₀).toNat
    kernelSubobject (d r k) =
      imageSubobject (Subobject.ofLE
        ((ssData k).Z ↑(n + 1)) ((ssData k).Z ↑n)
        ((ssData k).Z_anti (by exact_mod_cast Nat.le_succ n)) ≫
        (ssData k).pageπ ↑n)
  /-- 双次数 k 处 d_r 的像（视为页 E_r^{k + diffDeg r} = Z_n/B_n
      在 (k + diffDeg r) 处的子对象）等于该处
      B_{n+1} → Z_n → Z_n/B_n 的像。
      此处 n = (r - r₀).toNat。
      数学上：k + deg 处 im(d_r) = E_r^{k+deg} 内的 B_{r+1}/B_r。
      只对 r ≥ r₀ 陈述。 -/
  B_succ : ∀ (r : ℤ) (k : ι) (_ : r₀ ≤ r),
    let n := (r - r₀).toNat
    imageSubobject (d r k) =
      imageSubobject (Subobject.ofLE
        ((ssData (k + diffDeg r)).B ↑(n + 1)) ((ssData (k + diffDeg r)).Z ↑n)
        (le_trans ((ssData (k + diffDeg r)).B_le_Z ↑(n + 1))
          ((ssData (k + diffDeg r)).Z_anti (by exact_mod_cast Nat.le_succ n))) ≫
        (ssData (k + diffDeg r)).pageπ ↑n)

/-- 从预谱序列构造谱序列的构造函数：数据取自预谱序列 `P`，
    相容性证明（d²=0、Z_succ、B_succ）作为显式参数传入。
    这实现了数据与证明的彻底分离：调用方（如 FilteredComplex.toSpectralSequence）
    先构造 `toPreSS` 纯数据，再单独提供证明参数组装出谱序列。 -/
noncomputable def SpectralSequence.ofPreSS
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (P : PreSS C ι)
    (d_comp_d : ∀ (r : ℤ) (k : ι),
      P.d r k ≫ P.d r (k + P.diffDeg r) = 0)
    (Z_succ : ∀ (r : ℤ) (k : ι) (_ : P.r₀ ≤ r),
      let n := (r - P.r₀).toNat
      kernelSubobject (P.d r k) =
        imageSubobject (Subobject.ofLE
          ((P.ssData k).Z ↑(n + 1)) ((P.ssData k).Z ↑n)
          ((P.ssData k).Z_anti (by exact_mod_cast Nat.le_succ n)) ≫
          (P.ssData k).pageπ ↑n))
    (B_succ : ∀ (r : ℤ) (k : ι) (_ : P.r₀ ≤ r),
      let n := (r - P.r₀).toNat
      imageSubobject (P.d r k) =
        imageSubobject (Subobject.ofLE
          ((P.ssData (k + P.diffDeg r)).B ↑(n + 1)) ((P.ssData (k + P.diffDeg r)).Z ↑n)
          (le_trans ((P.ssData (k + P.diffDeg r)).B_le_Z ↑(n + 1))
            ((P.ssData (k + P.diffDeg r)).Z_anti (by exact_mod_cast Nat.le_succ n))) ≫
          (P.ssData (k + P.diffDeg r)).pageπ ↑n)) :
    SpectralSequence C ι where
  toPreSS := P
  d_comp_d := d_comp_d
  Z_succ := Z_succ
  B_succ := B_succ

/-- 谱序列的页对象 `E_r^k`，由嵌套子空间数据派生。
    这取代了原来存储的 `Page` 字段：页对象现在
    由 `(ssData k).page ↑(r - r₀).toNat` 计算。 -/
@[reducible] noncomputable def SpectralSequence.Page
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (E : SpectralSequence C ι) (r : ℤ) (k : ι) : C :=
  (E.ssData k).page ↑(r - E.r₀).toNat

/-- 谱序列的 E_r 页作为分次对象。 -/
noncomputable def SpectralSequence.pageGraded
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (E : SpectralSequence C ι) (r : ℤ) : GradedObject ι C :=
  E.Page r

/-! ### 子对象第三同构定理（pageHomologyIso 的辅助引理） -/

/-- 当 `P ≤ Q ≤ R` 时的典范满射 `cokernel(P → R) ⟶ cokernel(Q → R)`。 -/
noncomputable def Subobject.cokernelDesc_ofLE {V : C}
    (P Q R : Subobject V) (hPQ : P ≤ Q) (hQR : Q ≤ R) (hPR : P ≤ R := le_trans hPQ hQR) :
    cokernel (Subobject.ofLE P R hPR) ⟶ cokernel (Subobject.ofLE Q R hQR) :=
  cokernel.desc _ (cokernel.π (Subobject.ofLE Q R hQR)) (by
    have : Subobject.ofLE P R hPR = Subobject.ofLE P Q hPQ ≫ Subobject.ofLE Q R hQR :=
      (Subobject.ofLE_comp_ofLE P Q R hPQ hQR).symm
    rw [this, Category.assoc, cokernel.condition, comp_zero])

/-- 当 `P ≤ Q ≤ R` 时的典范单射 `cokernel(P → Q) ⟶ cokernel(P → R)`。 -/
noncomputable def Subobject.cokernelMap_ofLE {V : C}
    (P Q R : Subobject V) (hPQ : P ≤ Q) (hQR : Q ≤ R) (hPR : P ≤ R := le_trans hPQ hQR) :
    cokernel (Subobject.ofLE P Q hPQ) ⟶ cokernel (Subobject.ofLE P R hPR) :=
  cokernel.desc _ (Subobject.ofLE Q R hQR ≫ cokernel.π (Subobject.ofLE P R hPR)) (by
    rw [← Category.assoc, Subobject.ofLE_comp_ofLE, cokernel.condition])

/-- 子对象第三同构定理：当 `P ≤ Q ≤ R` 时 `(R/P) / (Q/P) ≅ R/Q`。
    用阿贝尔范畴结构构造。 -/
noncomputable def Subobject.thirdIso {V : C}
    (P Q R : Subobject V) (hPQ : P ≤ Q) (hQR : Q ≤ R) (hPR : P ≤ R := le_trans hPQ hQR) :
    cokernel (Subobject.cokernelMap_ofLE P Q R hPQ hQR hPR) ≅
      cokernel (Subobject.ofLE Q R hQR) :=
  -- 满射 φ : R/P → R/Q 的核是 Q/P，经 cokernelMap_ofLE 嵌入。
  -- 故 cokernel(cokernelMap_ofLE) = cokernel(Q/P → R/P) ≅ R/Q。
  -- 通过对该满射做 cokernel.desc 构造。
  { hom := cokernel.desc _ (Subobject.cokernelDesc_ofLE P Q R hPQ hQR hPR) (by
      -- cokernelMap_ofLE ≫ cokernelDesc_ofLE = 0
      -- cokernelMap_ofLE : Q/P → R/P
      -- cokernelDesc_ofLE : R/P → R/Q
      -- 合成：Q/P → R/Q 把 q 映到 q 在 R/Q 中的类 = 0，
      -- 因为 Q ≤ R，故 q 落在 R → R/Q 的核里。
      ext
      simp only [Subobject.cokernelMap_ofLE, Subobject.cokernelDesc_ofLE,
        cokernel.π_desc_assoc, comp_zero]
      rw [Category.assoc, cokernel.π_desc, cokernel.condition])
    inv := cokernel.desc _ (cokernel.π (Subobject.ofLE P R hPR) ≫
        cokernel.π (Subobject.cokernelMap_ofLE P Q R hPQ hQR hPR)) (by
      set f := Subobject.cokernelMap_ofLE P Q R hPQ hQR hPR
      have h1 : cokernel.π (Subobject.ofLE P Q hPQ) ≫ f =
          Subobject.ofLE Q R hQR ≫ cokernel.π (Subobject.ofLE P R hPR) :=
        cokernel.π_desc _ _ _
      calc Subobject.ofLE Q R hQR ≫ cokernel.π (Subobject.ofLE P R hPR) ≫ cokernel.π f
          = (Subobject.ofLE Q R hQR ≫ cokernel.π (Subobject.ofLE P R hPR)) ≫
              cokernel.π f := by rw [Category.assoc]
        _ = (cokernel.π (Subobject.ofLE P Q hPQ) ≫ f) ≫ cokernel.π f := by rw [h1]
        _ = cokernel.π (Subobject.ofLE P Q hPQ) ≫ (f ≫ cokernel.π f) := by
              rw [Category.assoc]
        _ = cokernel.π (Subobject.ofLE P Q hPQ) ≫ 0 := by rw [cokernel.condition]
        _ = 0 := comp_zero)
    hom_inv_id := by
      ext
      simp only [Category.comp_id, cokernel.π_desc,
        Subobject.cokernelDesc_ofLE, cokernel.π_desc_assoc]
    inv_hom_id := by
      ext
      simp only [Category.comp_id, Category.assoc, cokernel.π_desc_assoc,
        Subobject.cokernelDesc_ofLE, cokernel.π_desc] }

/-! ### 页短复形与同构 -/

/-- 页 `r` 上以源指标 `k` 为中心的短复形：
    `E_r^k → E_r^{k + diffDeg r} → E_r^{k + 2 * diffDeg r}`，
    零条件来自 `d_comp_d`。 -/
noncomputable def SpectralSequence.pageShortComplex
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (E : SpectralSequence C ι) (r : ℤ) (k : ι) : ShortComplex C :=
  ShortComplex.mk (E.d r k) (E.d r (k + E.diffDeg r)) (E.d_comp_d r k)

open CategoryTheory.Abelian in
/-- 阿贝尔范畴中 `e` 满射时 `imageSubobject (e ≫ f) = imageSubobject f`。 -/
private lemma imageSubobject_epi_comp {X₁ X₂ X₃ : C} (e : X₁ ⟶ X₂) [Epi e] (f : X₂ ⟶ X₃) :
    imageSubobject (e ≫ f) = imageSubobject f := by
  apply le_antisymm (imageSubobject_comp_le e f)
  have hle := imageSubobject_comp_le e f
  haveI : Epi (Subobject.ofLE _ _ hle) := imageSubobject_comp_le_epi_of_epi e f
  haveI : IsIso (Subobject.ofLE _ _ hle) := isIso_of_mono_of_epi _
  exact Subobject.le_of_comm (inv (Subobject.ofLE _ _ hle))
    (by rw [IsIso.inv_comp_eq]; exact (Subobject.ofLE_arrow hle).symm)

/-- `imageSubobject f ≤ kernelSubobject g` 时 `f ≫ g = 0`。 -/
private lemma comp_eq_zero_of_image_le_kernel {X₁ X₂ X₃ : C} (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃)
    (h : imageSubobject f ≤ kernelSubobject g) : f ≫ g = 0 := by
  rw [← imageSubobject_arrow_comp f, Category.assoc,
    show (imageSubobject f).arrow = Subobject.ofLE _ _ h ≫ (kernelSubobject g).arrow
      from (Subobject.ofLE_arrow h).symm,
    Category.assoc, kernelSubobject_arrow_comp, comp_zero, comp_zero]

/-- 分解：`ofLE Q R ≫ cokernel.π(P → R) = cokernel.π(P → Q) ≫ cokernelMap_ofLE`。 -/
private lemma factor_cokernelMap {V : C}
    (P Q R : Subobject V) (hPQ : P ≤ Q) (hQR : Q ≤ R) (hPR : P ≤ R := le_trans hPQ hQR) :
    Subobject.ofLE Q R hQR ≫ cokernel.π (Subobject.ofLE P R hPR) =
    cokernel.π (Subobject.ofLE P Q hPQ) ≫ Subobject.cokernelMap_ofLE P Q R hPQ hQR hPR := by
  simp [Subobject.cokernelMap_ofLE, cokernel.π_desc]

/-- 阿贝尔范畴中 `P ≤ Q ≤ R` 时 `cokernelMap_ofLE P Q R : Q/P → R/P` 是单射。
    用伪元素图表追踪证明。 -/
private instance cokernelMap_ofLE_mono {V : C}
    (P Q R : Subobject V) (hPQ : P ≤ Q) (hQR : Q ≤ R)
    (hPR : P ≤ R := le_trans hPQ hQR) :
    Mono (Subobject.cokernelMap_ofLE P Q R hPQ hQR hPR) := by
  open CategoryTheory.Abelian.Pseudoelement in
  refine mono_of_zero_of_map_zero _ fun a ha => ?_
  obtain ⟨q, hq⟩ := pseudo_surjective_of_epi (cokernel.π (Subobject.ofLE P Q hPQ)) a
  rw [← hq] at ha ⊢
  -- ha : cokernelMap_ofLE(cokernel.π(P→Q)(q)) = 0
  -- 需要：cokernel.π(P→R)(ofLE(Q,R)(q)) = 0
  have ha' : pseudoApply (cokernel.π (Subobject.ofLE P R hPR))
    (pseudoApply (Subobject.ofLE Q R hQR) q) = 0 := by
    have h1 := (Abelian.Pseudoelement.comp_apply
      (Subobject.ofLE Q R hQR) (cokernel.π (Subobject.ofLE P R hPR)) q).symm
    rw [h1, factor_cokernelMap P Q R hPQ hQR hPR, Abelian.Pseudoelement.comp_apply]; exact ha
  -- 造 P →[ofLE] R →[cokernel.π] cokernel 的正合性
  have hexact : (ShortComplex.mk (Subobject.ofLE P R hPR)
    (cokernel.π (Subobject.ofLE P R hPR)) (cokernel.condition _)).Exact :=
    ShortComplex.cokernelSequence_exact (Subobject.ofLE P R hPR)
  obtain ⟨p, hp⟩ := pseudo_exact_of_exact hexact _ ha'
  -- hp : pseudoApply (P.ofLE R hPR) p = pseudoApply (Q.ofLE R hQR) q
  have hp' : pseudoApply (Subobject.ofLE Q R hQR) (pseudoApply (Subobject.ofLE P Q hPQ) p) =
      pseudoApply (Subobject.ofLE Q R hQR) q := by
    rw [← Abelian.Pseudoelement.comp_apply, Subobject.ofLE_comp_ofLE]; exact hp
  have hinj := pseudo_injective_of_mono (Subobject.ofLE Q R hQR) hp'
  -- hinj : ofLE(P,Q)(p) = q。目标：cokernel.π(P→Q)(q) = 0
  rw [← hinj, ← Abelian.Pseudoelement.comp_apply, cokernel.condition, zero_apply]

/-- (E_r, d_r) 在指标 k 处的同调同构于 E_{r+1}^k。

    非形式证明梗概：`E_r = Z_r / B_r`。微分 `d_r` 的核是
    `Z_{r+1}/B_r`，像是 `B_{r+1}/B_r`（由嵌套定义）。
    故 `H(E_r, d_r) = (Z_{r+1}/B_r) / (B_{r+1}/B_r) ≅ Z_{r+1}/B_{r+1} = E_{r+1}`，
    由第三同构定理给出。

    短复形以源指标 `k - diffDeg r` 为中心，
    故同调在中间项即指标 `k` 处。 -/
noncomputable def SpectralSequence.pageHomologyIso
    {C : Type u} [Category.{v} C] [Abelian C]
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (E : SpectralSequence C ι) (r : ℤ) (k : ι) (hr : E.r₀ ≤ r) :
    E.Page (r + 1) k ≅ (E.pageShortComplex r (k - E.diffDeg r)).homology := by
  set n := (r - E.r₀).toNat with hn_def
  have hn1 : (r + 1 - E.r₀).toNat = n + 1 := by omega
  set S := E.pageShortComplex r (k - E.diffDeg r) with hS_def
  -- 在 D' = ssData(k - diffDeg r + diffDeg r) 中工作；命题上等于 ssData k
  set k' := k - E.diffDeg r + E.diffDeg r
  set D' := E.ssData k'
  have hk_eq : k' = k := sub_add_cancel k (E.diffDeg r)
  -- D' 的序事实
  have hBn_le_Bn1 : D'.B ↑n ≤ D'.B ↑(n + 1) := D'.B_mono (by exact_mod_cast Nat.le_succ n)
  have hBn1_le_Zn1 : D'.B ↑(n + 1) ≤ D'.Z ↑(n + 1) := D'.B_le_Z _
  have hZn1_le_Zn : D'.Z ↑(n + 1) ≤ D'.Z ↑n := D'.Z_anti (by exact_mod_cast Nat.le_succ n)
  have hBn_le_Zn1 : D'.B ↑n ≤ D'.Z ↑(n + 1) := le_trans hBn_le_Bn1 hBn1_le_Zn1
  -- LeftHomologyData 的关键态射
  -- i : Z_{n+1}/B_n → Z_n/B_n = S.X₂（单射，S.g 的核）
  set i := Subobject.cokernelMap_ofLE (D'.B ↑n) (D'.Z ↑(n + 1)) (D'.Z ↑n)
    hBn_le_Zn1 hZn1_le_Zn with hi_def
  -- π : Z_{n+1}/B_n → Z_{n+1}/B_{n+1} = D'.page(n+1)（满射，同调映射）
  set π_map := Subobject.cokernelDesc_ofLE (D'.B ↑n) (D'.B ↑(n + 1)) (D'.Z ↑(n + 1))
    hBn_le_Bn1 hBn1_le_Zn1 with hπ_def
  -- (wi) i ≫ S.g = 0：单射 Z_{n+1}/B_n ↪ Z_n/B_n 与 d_r 合成为零。
  -- 由 Z_succ：kernelSubobject(d_r) = imageSubobject(ofLE(Z_{n+1},Z_n) ≫ pageπ)。
  -- 由分解：该像等于 imageSubobject(i)（满射 ≫ i 给出同样的像）。
  -- 故 imageSubobject(i) = kernelSubobject(S.g)，于是 i ≫ S.g = 0。
  have wi : i ≫ S.g = 0 := by
    apply comp_eq_zero_of_image_le_kernel
    change imageSubobject i ≤ kernelSubobject (E.d r k')
    rw [E.Z_succ r k' hr,
      show Subobject.ofLE (D'.Z ↑(n + 1)) (D'.Z ↑n)
        (D'.Z_anti (by exact_mod_cast Nat.le_succ n)) ≫ D'.pageπ ↑n =
        cokernel.π (Subobject.ofLE (D'.B ↑n) (D'.Z ↑(n + 1)) hBn_le_Zn1) ≫ i
        from factor_cokernelMap _ _ _ _ _,
      imageSubobject_epi_comp]
  -- (hi) i 是 S.g 的核，经 kernelIsKernel 通过子对象等式
  -- Subobject.mk i = kernelSubobject(S.g) 转移证明。
  have heq_sub : Subobject.mk i = Subobject.mk (kernel.ι (E.d r k')) := by
    change Subobject.mk i = kernelSubobject (E.d r k')
    rw [E.Z_succ r k' hr,
      show Subobject.ofLE (D'.Z ↑(n + 1)) (D'.Z ↑n)
        (D'.Z_anti (by exact_mod_cast Nat.le_succ n)) ≫ D'.pageπ ↑n =
        cokernel.π (Subobject.ofLE (D'.B ↑n) (D'.Z ↑(n + 1)) hBn_le_Zn1) ≫ i
        from factor_cokernelMap _ _ _ _ _,
      imageSubobject_epi_comp, imageSubobject_mono]
  have hi : IsLimit (KernelFork.ofι i wi) := by
    apply (kernelIsKernel (E.d r k')).ofIsoLimit
    exact Fork.ext (Subobject.isoOfMkEqMk i (kernel.ι (E.d r k')) heq_sub).symm
      (Subobject.ofMkLEMk_comp heq_sub.ge)
  -- wπ 与 hπ 的公共基础设施：
  -- j : B_{n+1}/B_n → Z_{n+1}/B_n 是 cokernelMap_ofLE(B_n, B_{n+1}, Z_{n+1})
  set j := Subobject.cokernelMap_ofLE (D'.B ↑n) (D'.B ↑(n + 1)) (D'.Z ↑(n + 1))
    hBn_le_Bn1 hBn1_le_Zn1 with hj_def
  set f_lift := hi.lift (KernelFork.ofι S.f (by exact S.zero)) with hf_lift_def
  -- j ≫ π_map = 0，由第三同构定理
  have hj_π : j ≫ π_map = 0 := by
    simp only [j, π_map, Subobject.cokernelMap_ofLE, Subobject.cokernelDesc_ofLE]
    ext
    simp only [cokernel.π_desc_assoc, cokernel.π_desc, comp_zero,
      Category.assoc, cokernel.condition]
  have hBn_le_Zn : D'.B ↑(n + 1) ≤ D'.Z ↑n := le_trans hBn1_le_Zn1 hZn1_le_Zn
  -- 分解 ofLE(B_{n+1}, Z_n) ≫ pageπ n = cokernel.π(B_n→B_{n+1}) ≫ j ≫ i
  have hfactor : Subobject.ofLE (D'.B ↑(n + 1)) (D'.Z ↑n) hBn_le_Zn ≫ D'.pageπ ↑n =
      cokernel.π (Subobject.ofLE (D'.B ↑n) (D'.B ↑(n + 1)) hBn_le_Bn1) ≫ j ≫ i := by
    change Subobject.ofLE (D'.B ↑(n + 1)) (D'.Z ↑n) hBn_le_Zn ≫
      cokernel.π (Subobject.ofLE (D'.B ↑n) (D'.Z ↑n) (D'.B_le_Z ↑n)) = _
    rw [(Subobject.ofLE_comp_ofLE (D'.B ↑(n + 1)) (D'.Z ↑(n + 1)) (D'.Z ↑n)
      hBn1_le_Zn1 hZn1_le_Zn).symm,
      Category.assoc,
      factor_cokernelMap (D'.B ↑n) (D'.Z ↑(n + 1)) (D'.Z ↑n) hBn_le_Zn1 hZn1_le_Zn,
      ← Category.assoc (Subobject.ofLE (D'.B ↑(n + 1)) (D'.Z ↑(n + 1)) hBn1_le_Zn1),
      factor_cokernelMap (D'.B ↑n) (D'.B ↑(n + 1)) (D'.Z ↑(n + 1))
        hBn_le_Bn1 hBn1_le_Zn1,
      Category.assoc]
  -- S.f = f_lift ≫ i（由核叉积提升性质）
  have hfi : f_lift ≫ i = S.f :=
    hi.fac (KernelFork.ofι S.f (by exact S.zero)) WalkingParallelPair.zero
  -- 由 B_succ：imageSubobject(S.f) = imageSubobject(ofLE(B_{n+1},Z_n) ≫ pageπ n)
  have hB := E.B_succ r (k - E.diffDeg r) hr
  -- imageSubobject(f_lift ≫ i) = imageSubobject(j ≫ i)
  have him : imageSubobject (f_lift ≫ i) = imageSubobject (j ≫ i) := by
    rw [hfi]; change imageSubobject (E.d r (k - E.diffDeg r)) = _
    rw [hB, hfactor, imageSubobject_epi_comp]
  -- j ≫ i 单射，故 imageSubobject(j ≫ i) = Subobject.mk(j ≫ i)
  have hjim : imageSubobject (j ≫ i) = Subobject.mk (j ≫ i) := imageSubobject_mono _
  have hle : imageSubobject (f_lift ≫ i) ≤ Subobject.mk (j ≫ i) := him ▸ hjim ▸ le_refl _
  have hfact_ji : (Subobject.mk (j ≫ i)).Factors (f_lift ≫ i) := by
    apply Subobject.factors_of_le _ hle
    have := imageSubobject_factors_comp_self (f := f_lift ≫ i) (𝟙 _)
    simpa using this
  -- 提取分解映射并证 f_lift = (满射因子) ≫ j
  set φ_ji := (Subobject.mk (j ≫ i)).factorThru (f_lift ≫ i) hfact_ji
  have hφ_ji : φ_ji ≫ (Subobject.mk (j ≫ i)).arrow = f_lift ≫ i :=
    Subobject.factorThru_arrow _ _ _
  have harrow_ji : (Subobject.mk (j ≫ i)).arrow =
      (Subobject.underlyingIso (j ≫ i)).hom ≫ (j ≫ i) :=
    (Subobject.underlyingIso_hom_comp_eq_mk (j ≫ i)).symm
  -- ψ ≫ j = f_lift，其中 ψ = φ_ji ≫ underlyingIso.hom
  set ψ := φ_ji ≫ (Subobject.underlyingIso (j ≫ i)).hom with hψ_def
  have hψ_j : ψ ≫ j = f_lift := by
    apply (cancel_mono i).mp
    rw [Category.assoc]
    change ψ ≫ (j ≫ i) = f_lift ≫ i
    change (φ_ji ≫ (Subobject.underlyingIso (j ≫ i)).hom) ≫ (j ≫ i) = f_lift ≫ i
    rw [Category.assoc, ← harrow_ji, hφ_ji]
  -- (wπ) f_lift ≫ π_map = 0
  have wπ : f_lift ≫ π_map = 0 := by
    calc f_lift ≫ π_map
        = (ψ ≫ j) ≫ π_map :=
          congrArg (fun q => q ≫ π_map) hψ_j.symm
      _ = ψ ≫ (j ≫ π_map) := by rw [Category.assoc]
      _ = ψ ≫ 0 := by rw [hj_π]
      _ = 0 := comp_zero
  -- (hπ) π_map 是 f_lift 的余核。
  -- 关键：ψ 把 f_lift 分解过 j。对任意满足 f_lift ≫ g = 0 的 g，
  -- 得 j ≫ g = 0（因 ψ 足够满），再用 j 的余核。
  -- 具体：用 factorThruImageSubobject 得到满射因子。
  have hπ : IsColimit (CokernelCofork.ofπ π_map wπ) := by
    -- 策略：ψ 满 且 f_lift = ψ ≫ j，故 cokernel(f_lift) ≅ cokernel(j)。
    -- 于是 π_map = cokernel.π(j) ≫ thirdIso.hom 给出 f_lift 的余核。
    -- 第一步：证 ψ 满。
    have hφ_eq : φ_ji = factorThruImageSubobject (f_lift ≫ i) ≫
        (Subobject.isoOfEq _ _ (him.trans hjim)).hom := by
      apply (cancel_mono (Subobject.mk (j ≫ i)).arrow).mp
      rw [hφ_ji, Category.assoc, Subobject.isoOfEq_hom, Subobject.ofLE_arrow,
        imageSubobject_arrow_comp]
    have hψ_epi : Epi ψ := by
      rw [hψ_def, hφ_eq, Category.assoc]
      exact epi_comp _ _
    -- 关键：cokernel.π(j) ≫ thirdIso.hom = π_map
    have hπ_factor : cokernel.π j ≫
        (Subobject.thirdIso (D'.B ↑n) (D'.B ↑(n + 1)) (D'.Z ↑(n + 1))
          hBn_le_Bn1 hBn1_le_Zn1).hom = π_map :=
      cokernel.π_desc _ _ _
    set thirdIso := Subobject.thirdIso (D'.B ↑n) (D'.B ↑(n + 1)) (D'.Z ↑(n + 1))
      hBn_le_Bn1 hBn1_le_Zn1 with hthirdIso_def
    -- 对任意满足 f_lift ≫ s.π = 0 ≫ s.π 的余核叉积 s，有 j ≫ s.π = 0
    have hjs : ∀ (s : Cofork f_lift 0), j ≫ Cofork.π s = 0 := by
      intro s
      haveI := hψ_epi
      apply zero_of_epi_comp ψ
      rw [← Category.assoc, hψ_j]
      have := s.condition  -- f_lift ≫ s.π = 0 ≫ s.π
      simp only [zero_comp] at this
      exact this
    -- 第二步：用 Cofork.IsColimit.mk 造余极限
    exact Cofork.IsColimit.mk _
      (fun s => thirdIso.inv ≫ cokernel.desc j (Cofork.π s) (hjs s))
      (fun s => by
        -- 需要：π_map ≫ (thirdIso.inv ≫ cokernel.desc j (s.π) _) = s.π
        change π_map ≫ thirdIso.inv ≫ cokernel.desc j (Cofork.π s) (hjs s) = Cofork.π s
        rw [show π_map = cokernel.π j ≫ thirdIso.hom from hπ_factor.symm,
          Category.assoc, thirdIso.hom_inv_id_assoc, cokernel.π_desc])
      (fun s m hm => by
        -- 需要：m = thirdIso.inv ≫ cokernel.desc j (s.π) _
        change m = thirdIso.inv ≫ cokernel.desc j (Cofork.π s) (hjs s)
        apply (cancel_epi thirdIso.hom).mp
        rw [thirdIso.hom_inv_id_assoc]
        -- 目标：thirdIso.hom ≫ m = cokernel.desc j (s.π) _
        apply (cancel_epi (cokernel.π j)).mp
        rw [cokernel.π_desc, ← Category.assoc, hπ_factor]
        exact hm)
  -- 组装 LeftHomologyData
  set h : S.LeftHomologyData := {
    K := cokernel (Subobject.ofLE (D'.B ↑n) (D'.Z ↑(n + 1)) hBn_le_Zn1)
    H := D'.page ↑(n + 1)
    i := i
    π := π_map
    wi := wi
    hi := hi
    wπ := wπ
    hπ := hπ
  }
  -- 左边经转移等于 h.H：E.Page (r+1) k = D.page ↑(n+1) = D'.page ↑(n+1) = h.H
  have hPageH : E.Page (r + 1) k = h.H := by
    change (E.ssData k).page ↑((r + 1 - E.r₀).toNat) = D'.page ↑(n + 1)
    rw [hn1]; congr 1; exact hk_eq.symm ▸ rfl
  exact eqToIso hPageH ≪≫ h.homologyIso.symm

/-! ### E∞ 页 -/

/-- 若所有页 `E_r^k = 0`（r ≥ r₀），则 `E∞^k = 0`。

    证明：对所有 `r ≥ r₀` 有 `E_r = Z_r/B_r = 0`，即 `Z_r = B_r`
    （包含 `B_r ↪ Z_r` 的余核消失当且仅当该包含满，
    在阿贝尔范畴中即 `B_r = Z_r`）。
    因对所有 r 有 `Z ⊤ ≤ Z_r = B_r ≤ B ⊤`，且 `B ⊤ ≤ Z ⊤`
    （由 `B_le_Z` 在 ⊤ 处），得 `Z ⊤ = B ⊤`，故 `E∞ = Z⊤/B⊤ = 0`。 -/
theorem SpectralSequence.eInfty_isZero_of_page_isZero
    {C : Type*} [Category C] [Abelian C]
    {α : Type*} [AddCommGroup α] [DecidableEq α]
    (E : SpectralSequence C α) (k : α)
    (h : ∀ r : ℤ, E.r₀ ≤ r → IsZero (E.Page r k)) :
    IsZero ((E.ssData k).eInfty) := by
  unfold SSData.eInfty
  apply SSData.page_isZero_of_eq
  set D := E.ssData k
  apply le_antisymm
  · exact D.B_le_Z ⊤
  · have hpage0 : IsZero (D.page (↑(0 : ℕ))) := by
      have := h E.r₀ (le_refl _)
      simp only [SpectralSequence.Page, SSData.page] at this
      have hrr : (E.r₀ - E.r₀).toNat = 0 := by omega
      rw [hrr] at this
      exact this
    have hBZ : D.B ↑(0 : ℕ) = D.Z ↑(0 : ℕ) := D.eq_of_page_isZero _ hpage0
    calc D.Z ⊤ ≤ D.Z ↑(0 : ℕ) := D.Z_anti le_top
      _ = D.B ↑(0 : ℕ) := hBZ.symm
      _ ≤ D.B ⊤ := D.B_mono le_top

/-- 谱序列在页 `N` 处退化，如果对所有 r ≥ N 微分 d_r = 0。 -/
def SpectralSequence.DegeneratesAt
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (E : SpectralSequence C ι) (N : ℤ) : Prop :=
  ∀ (r : ℤ), N ≤ r → ∀ (k : ι), E.d r k = 0

/-! ### 谱序列的态射 -/

/-- 谱序列的态射是每个双次数上底层对象 `V` 之间的映射族，
    保持循环 `Z_r`、边缘 `B_r`，并与微分交换。 -/
structure SpectralSequenceMorphism
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (E E' : SpectralSequence C ι)
    extends PreSSMorphism E.toPreSS E'.toPreSS

/-! 同构的短复形诱导同构的中间同调。这个引理把逐页归纳中
    “短复形层面的同构性”与 mathlib 的左同调接口接起来。 -/
theorem ShortComplex.isIso_leftHomologyMap_of_iso
    {C : Type u} [Category.{v} C] [Abelian C]
    {S₁ S₂ : ShortComplex C} (e : S₁ ≅ S₂) [S₁.HasLeftHomology]
    [S₂.HasLeftHomology] : IsIso (S₁.leftHomologyMap e.hom) := by
  infer_instance

/-! 交换的同调比较方块把同调层面的同构传回页面。 -/
theorem isIso_of_pageHomologyIso_square
    {C : Type u} [Category.{v} C]
    {A B H K : C} (eA : A ≅ H) (eB : B ≅ K)
    (f : A ⟶ B) (g : H ⟶ K) [IsIso g]
    (h : eA.hom ≫ g = f ≫ eB.hom) : IsIso f := by
  have hf : f = eA.hom ≫ g ≫ eB.inv := by
    apply (cancel_mono eB.hom).1
    rw [← h]
    simp only [Category.assoc, eB.inv_hom_id, Category.comp_id]
  rw [hf]
  infer_instance

/-- 谱序列态射经 `cokernel.map` 诱导 E∞ 页上的映射。 -/
noncomputable def SpectralSequenceMorphism.eInftyMap
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {E E' : SpectralSequence C ι} (f : SpectralSequenceMorphism E E') (k : ι) :
    (E.ssData k).eInfty ⟶ (E'.ssData k).eInfty := by
  unfold SSData.eInfty SSData.page
  exact cokernel.map
    (Subobject.ofLE ((E.ssData k).B ⊤) ((E.ssData k).Z ⊤) ((E.ssData k).B_le_Z ⊤))
    (Subobject.ofLE ((E'.ssData k).B ⊤) ((E'.ssData k).Z ⊤) ((E'.ssData k).B_le_Z ⊤))
    (f.preserves_B k ⊤).choose
    (f.preserves_Z k ⊤).choose
    (by
      have hB := (f.preserves_B k ⊤).choose_spec
      have hZ := (f.preserves_Z k ⊤).choose_spec
      apply (cancel_mono ((E'.ssData k).Z ⊤).arrow).mp
      simp only [Category.assoc, hZ, Subobject.ofLE_arrow, hB, Subobject.ofLE_arrow_assoc])

/-! ### E∞ 数据 -/

/-- 打包一个谱序列并为其 E∞ 页提供便捷访问。
    包装 `SpectralSequence` 以提供统一的 `EInfty` 访问器，
    供下游公理（Adams SS、Synthetic Adams SS）使用。 -/
structure EInftyData (C : Type u) [Category.{v} C] [Abelian C]
    (ι : Type w) [AddCommGroup ι] [DecidableEq ι] where
  /-- 底层谱序列 -/
  ss : SpectralSequence C ι

/-- 双次数 `k` 处的 E∞ 页，定义为底层 SSData 的 E∞。 -/
noncomputable def EInftyData.EInfty {C : Type u} [Category.{v} C] [Abelian C]
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (eData : EInftyData C ι) (k : ι) : C :=
  (eData.ss.ssData k).eInfty

/-! ### PreSS 的范畴结构与忘形函子 -/

/-- underlying 态射的外延性：两态射 φ 分量相同则相等
    （UnderlyingMorphism 只有 φ 一个字段）。 -/
@[ext]
theorem UnderlyingMorphism.ext
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {D D' : ι → SSData C} {f g : UnderlyingMorphism ι D D'}
    (h : f.φ = g.φ) : f = g := by
  rcases f with ⟨f_φ⟩
  rcases g with ⟨g_φ⟩
  congr!

/-- `SSDataMorphism` 由底层映射族唯一决定；保 `B/Z` 字段都是命题。 -/
@[ext]
theorem SSDataMorphism.ext
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {D D' : ι → SSData C} {f g : SSDataMorphism ι D D'}
    (h : f.φ = g.φ) : f = g := by
  rcases f with ⟨⟨fφ⟩, _, _⟩
  rcases g with ⟨⟨gφ⟩, _, _⟩
  dsimp only at h
  subst h
  rfl

/-- 预谱序列态射的外延性：两态射 φ 分量相同则相等。
    preserves_Z / preserves_B / comm_d 都是 ∃ 命题（Prop），
    由 proof irrelevance 自动相等；用 cases 沿 extends 链逐层消去构造子
    （Prop 字段只引入不展开），得到底层变量方程后 subst。 -/
@[ext]
theorem PreSSMorphism.ext
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {E E' : PreSS C ι} {f g : PreSSMorphism E E'}
    (h : f.φ = g.φ) : f = g := by
  rcases f with ⟨f_sd, _, _, _⟩
  rcases g with ⟨g_sd, _, _, _⟩
  have hsd : f_sd = g_sd := SSDataMorphism.ext h
  subst hsd
  rfl

/-- 谱序列态射的外延性：两态射 φ 分量相同则相等（其余字段都是 Prop）。
    先 rcases 出构造子再 congr，避免 cases 对 ∃ 字段的依值消去失败。 -/
@[ext]
theorem SpectralSequenceMorphism.ext
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {E E' : SpectralSequence C ι} {f g : SpectralSequenceMorphism E E'}
    (h : f.φ = g.φ) : f = g := by
  rcases f with ⟨f_pre⟩
  rcases g with ⟨g_pre⟩
  congr 1
  exact PreSSMorphism.ext h

/-- SSData 分次族的打包：忘形函子的目标范畴的对象，
    即一个 `ι → SSData C` 族（忘掉 r₀、diffDeg、d 之后剩下的东西）。 -/
structure GradedSSData (C : Type u) [Category.{v} C] [Abelian C]
    (ι : Type w) [AddCommGroup ι] [DecidableEq ι] where
  /-- 每个双次数上的 SSData -/
  data : ι → SSData C

/-- SSData 分次族的范畴结构：态射为 UnderlyingMorphism，
    恒等与复合均由 φ 分量逐点给出。 -/
instance {ι : Type w} [AddCommGroup ι] [DecidableEq ι] :
    Category.{max w v} (GradedSSData C ι) where
  Hom D D' := UnderlyingMorphism ι D.data D'.data
  id D := ⟨fun k => 𝟙 _⟩
  comp f g := ⟨fun k => f.φ k ≫ g.φ k⟩
  id_comp f := UnderlyingMorphism.ext (funext fun k => Category.id_comp (f.φ k))
  comp_id f := UnderlyingMorphism.ext (funext fun k => Category.comp_id (f.φ k))
  assoc f g h :=
    UnderlyingMorphism.ext (funext fun k => Category.assoc (f.φ k) (g.φ k) (h.φ k))

/-- 预谱序列的范畴结构：态射为 PreSSMorphism。
    恒等态射的 φ 为恒等，复合的 φ 为分量复合；
    保 Z/B 的提升取两次提升的复合（用 choose 取出存在见证），
    微分交换条件取页上映射的复合。范畴公理由 ext 归约到 φ 分量。 -/
instance {ι : Type w} [AddCommGroup ι] [DecidableEq ι] :
    Category.{max w v} (PreSS C ι) where
  Hom E E' := PreSSMorphism E E'
  id X := by
    let f : SSDataMorphism ι X.ssData X.ssData := {
      φ := fun _ => 𝟙 _
      preserves_Z := fun _ _ => ⟨𝟙 _, by simp⟩
      preserves_B := fun _ _ => ⟨𝟙 _, by simp⟩ }
    refine { toSSDataMorphism := f, r₀_eq := rfl, diffDeg_eq := rfl, comm_d := ?_ }
    intro r k
    dsimp only
    simp only [SSDataMorphism.pageMapOfEq]
    rw [f.pageMap_eq_id k _ rfl, f.pageMap_eq_id (k + X.diffDeg r) _ rfl]
    simp
  comp {X Y Z} f g := by
    let h : SSDataMorphism ι _ _ := {
      φ := fun k => f.φ k ≫ g.φ k
      preserves_Z := fun k r =>
        ⟨(f.preserves_Z k r).choose ≫ (g.preserves_Z k r).choose, by
          rw [Category.assoc, (g.preserves_Z k r).choose_spec,
            ← Category.assoc, (f.preserves_Z k r).choose_spec, Category.assoc]⟩
      preserves_B := fun k r =>
        ⟨(f.preserves_B k r).choose ≫ (g.preserves_B k r).choose, by
          rw [Category.assoc, (g.preserves_B k r).choose_spec,
            ← Category.assoc, (f.preserves_B k r).choose_spec, Category.assoc]⟩ }
    refine ⟨h, Eq.trans f.r₀_eq g.r₀_eq,
      Eq.trans f.diffDeg_eq g.diffDeg_eq, ?_⟩
    intro r k
    have hf := f.comm_d r k
    have hg := g.comm_d r k
    dsimp only at hf hg ⊢
    let nX : WithTop ℕ := ↑(r - X.r₀).toNat
    let nY : WithTop ℕ := ↑(r - Y.r₀).toNat
    let nZ : WithTop ℕ := ↑(r - Z.r₀).toNat
    let hnXY : nX = nY := congrArg
      (fun r₀ => (↑(r - r₀).toNat : WithTop ℕ)) f.r₀_eq
    let hnYZ : nY = nZ := congrArg
      (fun r₀ => (↑(r - r₀).toNat : WithTop ℕ)) g.r₀_eq
    let hkXY : k + X.diffDeg r = k + Y.diffDeg r :=
      congrArg (fun d => k + d) (congrFun f.diffDeg_eq r)
    let hkYZ : k + Y.diffDeg r = k + Z.diffDeg r :=
      congrArg (fun d => k + d) (congrFun g.diffDeg_eq r)
    have hpage := SSDataMorphism.pageMapOfEq_comp
      f.toSSDataMorphism g.toSSDataMorphism h
      k k k rfl rfl nX nY nZ hnXY hnYZ rfl
    have hpageShift := SSDataMorphism.pageMapOfEq_comp
      f.toSSDataMorphism g.toSSDataMorphism h
      (k + X.diffDeg r) (k + Y.diffDeg r) (k + Z.diffDeg r)
      hkXY hkYZ nX nY nZ hnXY hnYZ rfl
    rw [hpage, hpageShift]
    simp only [Category.assoc]
    rw [hg, ← Category.assoc, hf, Category.assoc]
  id_comp f := PreSSMorphism.ext (funext fun k => Category.id_comp (f.φ k))
  comp_id f := PreSSMorphism.ext (funext fun k => Category.comp_id (f.φ k))
  assoc f g h :=
    PreSSMorphism.ext (funext fun k => Category.assoc (f.φ k) (g.φ k) (h.φ k))

/-- 忘形函子：把预谱序列送到其 SSData 分次族
    （忘掉 r₀、diffDeg、d 与所有证明条件），
    态射送到其 underlying 态射（只记住 φ）。 -/
def PreSS.forget {ι : Type w} [AddCommGroup ι] [DecidableEq ι] :
    PreSS C ι ⥤ GradedSSData C ι where
  obj E := ⟨E.ssData⟩
  map f := ⟨(f : PreSSMorphism _ _).φ⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- 忘形函子是忠实的（faithful）：PreSSMorphism 由其 φ 唯一决定，
    因为其余字段都是 Prop（proof irrelevance）。 -/
instance {ι : Type w} [AddCommGroup ι] [DecidableEq ι] :
    Functor.Faithful (PreSS.forget (C := C) (ι := ι)) where
  map_injective h := PreSSMorphism.ext
    (congrArg (fun m : UnderlyingMorphism _ _ _ => m.φ) h)

/-! ### 谱序列的范畴与全子范畴 -/

/-- 谱序列态射的恒等态射，由预谱序列的恒等态射提升。 -/
def SpectralSequenceMorphism.id
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (E : SpectralSequence C ι) : SpectralSequenceMorphism E E :=
  ⟨(𝟙 E.toPreSS : PreSSMorphism E.toPreSS E.toPreSS)⟩

/-- 谱序列态射的复合，由预谱序列态射的复合提升。 -/
def SpectralSequenceMorphism.comp
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {E₁ E₂ E₃ : SpectralSequence C ι}
    (f : SpectralSequenceMorphism E₁ E₂)
    (g : SpectralSequenceMorphism E₂ E₃) :
    SpectralSequenceMorphism E₁ E₃ :=
  ⟨@CategoryStruct.comp (PreSS C ι)
    (instCategoryPreSS (C := C) (ι := ι)).toCategoryStruct
    E₁.toPreSS E₂.toPreSS E₃.toPreSS
    f.toPreSSMorphism g.toPreSSMorphism⟩

/-- 谱序列的范畴结构：态射为 SpectralSequenceMorphism。
    恒等与复合的 φ 逐分量给出；保 Z/B 的提升取两次见证提升的复合，
    微分交换取页上映射的复合。范畴公理由 ext 归约到 φ 分量。 -/
instance {ι : Type w} [AddCommGroup ι] [DecidableEq ι] :
    Category.{max w v} (SpectralSequence C ι) where
  Hom E E' := SpectralSequenceMorphism E E'
  id E := SpectralSequenceMorphism.id E
  comp f g := SpectralSequenceMorphism.comp f g
  id_comp f := SpectralSequenceMorphism.ext (funext fun k => by
    simp [SpectralSequenceMorphism.id, SpectralSequenceMorphism.comp])
  comp_id f := SpectralSequenceMorphism.ext (funext fun k => by
    simp [SpectralSequenceMorphism.id, SpectralSequenceMorphism.comp])
  assoc f g h := SpectralSequenceMorphism.ext (funext fun k => by
    simp [SpectralSequenceMorphism.comp, Category.assoc])

@[simp]
theorem SpectralSequence.comp_φ
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {E₁ E₂ E₃ : SpectralSequence C ι}
    (f : E₁ ⟶ E₂) (g : E₂ ⟶ E₃) (k : ι) :
    (f ≫ g).φ k = f.φ k ≫ g.φ k :=
  rfl

/-- 谱序列态射与（经 toPreSS 遗忘证明条件后的）预谱序列态射之间的等价：
    两边字段逐字相同（φ、preserves_Z、preserves_B、comm_d，
    且 `E.toPreSS.ssData` 与 `E.ssData` 定义上相等、
    `PreSS.Page` 与 `SpectralSequence.Page` 同为可约定义），
    来回映射都只是逐字段搬运，故为等价。
    往返恒等式直接在定义上展开后由 congr 逐字段解决。 -/
def SpectralSequenceMorphism.equivPreSSMorphism
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (E E' : SpectralSequence C ι) :
    SpectralSequenceMorphism E E' ≃ PreSSMorphism E.toPreSS E'.toPreSS where
  toFun f := f.toPreSSMorphism
  invFun g := ⟨g⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- 谱序列到预谱序列的包含函子：对象经 `toPreSS` 遗忘证明条件，
    态射经上述等价的前向映射（字段逐字保留）。
    map_id / map_comp 展开到 φ 分量后由 rfl 成立。 -/
def SpectralSequence.inclusion {ι : Type w} [AddCommGroup ι] [DecidableEq ι] :
    SpectralSequence C ι ⥤ PreSS C ι where
  obj E := E.toPreSS
  map := by
    intro E E' f
    change SpectralSequenceMorphism E E' at f
    exact f.toPreSSMorphism
  map_id _ := PreSSMorphism.ext rfl
  map_comp _ _ := PreSSMorphism.ext (by funext k; rfl)

/-- 包含函子忠实：谱序列态射由其 φ 唯一决定。 -/
instance {ι : Type w} [AddCommGroup ι] [DecidableEq ι] :
    Functor.Faithful (SpectralSequence.inclusion (C := C) (ι := ι)) where
  map_injective := by
    intro E E' f g h
    change SpectralSequenceMorphism E E' at f g
    change f.toPreSSMorphism = g.toPreSSMorphism at h
    exact SpectralSequenceMorphism.ext
      (congrArg (fun m : PreSSMorphism _ _ => m.φ) h)

/-- 包含函子满（full）：任意预谱序列态射可经等价的逆映射
    拉回为谱序列态射（字段逐字搬运）。 -/
instance {ι : Type w} [AddCommGroup ι] [DecidableEq ι] :
    Functor.Full (SpectralSequence.inclusion (C := C) (ι := ι)) where
  map_surjective := by
    intro E E' g
    change PreSSMorphism E.toPreSS E'.toPreSS at g
    exact ⟨⟨g⟩, rfl⟩

/-- 结论：谱序列是预谱序列的全子范畴——
    包含函子既忠实（faithful）又满（full），故全忠实（fully faithful）。 -/
noncomputable def SpectralSequence.inclusionFullyFaithful
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι] :
    (SpectralSequence.inclusion (C := C) (ι := ι)).FullyFaithful :=
  Functor.FullyFaithful.ofFullyFaithful _

/-! ### 谱序列范畴中的交换图 -/

/-- 谱序列范畴中的交换方块 `SpectralSequence.CommSq`：
    四个谱序列 `W X Y Z` 与四个谱序列态射之间的 `CommSq` 断言，
    即 `f ≫ h = g ≫ i`（谱序列态射相等）。 -/
abbrev SpectralSequence.CommSq
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {W X Y Z : SpectralSequence C ι}
    (f : W ⟶ X) (g : W ⟶ Y) (h : X ⟶ Z) (i : Y ⟶ Z) : Prop :=
  CategoryTheory.CommSq f g h i

/-- 交换性只需在 underlying 层面验证：
    谱序列中 `CommSq f g h i` 成立，当且仅当四个态射的
    underlying φ 映射族（`GradedSSData` 中的态射）组成交换方块，
    即逐双次数 `f.φ k ≫ h.φ k = g.φ k ≫ i.φ k`。
    这是因为谱序列范畴的复合由 φ 分量逐点给出，
    且态射相等由 `SpectralSequenceMorphism.ext` 归约到 φ 分量相等。 -/
theorem SpectralSequence.commSq_iff_underlying
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {W X Y Z : SpectralSequence C ι}
    (f : W ⟶ X) (g : W ⟶ Y) (h : X ⟶ Z) (i : Y ⟶ Z) :
    SpectralSequence.CommSq f g h i ↔
      ∀ (k : ι), f.φ k ≫ h.φ k = g.φ k ≫ i.φ k := by
  constructor
  · intro hsq k
    -- 底层交换性：从谱序列态射等式取 φ 分量后逐点取值
    simpa only [SpectralSequence.comp_φ] using congrFun
      (congrArg (fun m : SpectralSequenceMorphism W Z => m.φ) hsq.w) k
  · intro hsq
    constructor
    -- 由 underlying 层逐点交换性经 ext 反推谱序列态射相等
    apply SpectralSequenceMorphism.ext
    funext k
    simpa only [SpectralSequence.comp_φ] using hsq k

/-- 若底层 SS 在双次数 `k` 处每一页都为零，则 E∞ 为零。 -/
noncomputable def EInftyData.eInfty_isZero_of_page_isZero
    {C : Type u} [Category.{v} C] [Abelian C]
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (eData : EInftyData C ι) (k : ι)
    (h : ∀ r : ℤ, eData.ss.r₀ ≤ r → IsZero (eData.ss.Page r k)) :
    IsZero (eData.EInfty k) :=
  SpectralSequence.eInfty_isZero_of_page_isZero eData.ss k h

end KIPBase.SpectralSequence
