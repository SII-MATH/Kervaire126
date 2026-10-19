/-
  KIPBase.SpectralSequence.Elementwise
  §1.1 补全：有限页逐元素呈现（finite-page elementwise presentation）

  Blueprint: spectral_sequences.tex, def:ss-elementwise-page-presentation
  （原缺口 1，blueprint 中标注 \notready 且无 \lean 目标）

  本文件把内部 `SSData`/`SpectralSequence`（嵌套子对象模型）展开为
  AIM 论文 main.tex:827-862 的逐元素 Z/B 机器：

    * 循环/边界子对象 Z_r, B_r（直接来自 SSData，含 Adams 页码重编号
      cycleLevel(r) = r - 1：显示页 E_r 对应 Z_{r-1}/B_{r-1}）；
    * 页同构  E_r ≅ Z_{r-1}/B_{r-1}（内部恒等识别，因为
      `SpectralSequence.Page` 就定义为这个商）；
    * 提升微分  d̃_r : Z_{r-1} ⟶ E_2/B_{r-1}（由范畴化页微分经
      商映射分解得到），并证明：
        - d̃_r 在 B_{r-1} 上消失（故诱导回页微分 d_r）；
        - d̃_r 的核（作为 Z_{r-1} 的子对象）恰为 Z_r 的像；
        - d̃_r 的像恰为 B_r/B_{r-1}（B_succ 的逐元素重述）。

  严禁使用 Mathlib 的 `CategoryTheory.SpectralSequence` 或
  `CategoryTheory.*.SpectralObject`：本文件只依赖 KIPBase 自建的
  嵌套子对象模型（Basic.lean）与 Mathlib 的一般阿贝尔范畴/子对象 API。
-/
import KIPBase.SpectralSequence.Basic

namespace KIPBase.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v w

set_option linter.dupNamespace false

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι : Type w} [AddCommGroup ι] [DecidableEq ι]

/-! ### Adams 页码重编号

内部 `SSData` 用 `n = (r - r₀).toNat` 索引循环/边界层（`Z 0 = ⊤` 起步），
而 AIM/Adams 约定显示页 `E_r` 对应 `Z_{r-1}/B_{r-1}`（`Z_1 = E_2` 起步）。
对 `r₀ = 2` 的谱序列两者一致：`n = r - 2 = cycleLevel(r) - 1 …` 的换算
由 `PageLevelConvention.cycleLevel` 记录（见 Blueprint.lean）。
本节所有构造都在内部索引 `n` 上进行，并通过 `SpectralSequence.Page`
的约简（`Page r k = (ssData k).page ↑(r - r₀).toNat`）与显示页认同。 -/

namespace Elementwise

variable (E : SpectralSequence C ι)

/-- 双次数 `k` 处的循环子对象：第 `r` 页（`r ≥ r₀`）的循环是
`Z_{(r-r₀)}`，即 SSData 在重编号后的层。 -/
noncomputable def cycleSub (k : ι) (r : ℤ) : Subobject (E.ssData k).V :=
  (E.ssData k).Z ↑(r - E.r₀).toNat

/-- 双次数 `k` 处的边界子对象：同一重编号。 -/
noncomputable def boundarySub (k : ι) (r : ℤ) : Subobject (E.ssData k).V :=
  (E.ssData k).B ↑(r - E.r₀).toNat

/-- 页同构：显示页 `E_r^k` 按定义就是 `Z_n/B_n`（`n = (r-r₀).toNat`）。
这是内部恒等识别，不是外部构造。 -/
noncomputable def pageIsoCycles (r : ℤ) (k : ι) :
    E.Page r k ≅
      cokernel (Subobject.ofLE (boundarySub E k r) (cycleSub E k r)
        ((E.ssData k).B_le_Z _)) :=
  Iso.refl _

/-- 嵌套链：边界含于循环。 -/
theorem boundary_le_cycle (k : ι) (r : ℤ) :
    boundarySub E k r ≤ cycleSub E k r :=
  (E.ssData k).B_le_Z _

/-- 嵌套链：下一页循环含于本页循环（`Z` 反单调的重述）。 -/
theorem cycle_succ_le (k : ι) (r : ℤ) (hr : E.r₀ ≤ r) :
    (E.ssData k).Z ↑((r + 1 - E.r₀).toNat) ≤ cycleSub E k r :=
  (E.ssData k).Z_anti (by
    have : (r + 1 - E.r₀).toNat = (r - E.r₀).toNat + 1 := by omega
    rw [this]
    exact_mod_cast Nat.le_succ _)

/-- 嵌套链：本页边界含于下一页边界（`B` 单调的重述）。 -/
theorem boundary_le_succ (k : ι) (r : ℤ) (hr : E.r₀ ≤ r) :
    boundarySub E k r ≤ (E.ssData k).B ↑((r + 1 - E.r₀).toNat) :=
  (E.ssData k).B_mono (by
    have : (r + 1 - E.r₀).toNat = (r - E.r₀).toNat + 1 := by omega
    rw [this]
    exact_mod_cast Nat.le_succ _)

end Elementwise

/-! ### 提升微分 d̃_r

范畴化页微分是 `E.d r k : E_r^k ⟶ E_r^{k+deg}`，其中
`E_r^k = Z_n/B_n`（`n = (r-r₀).toNat`）。
提升微分把它沿商投影 `Z_n ⟶ Z_n/B_n` 拉回为从循环子对象出发的映射：

  d̃_r : (Z_n).underlying ⟶ E_r^{k+deg}

即 `pageπ n ≫ d r k` 的复合。下面证明其在 `B_n` 上消失；
其核为 `Z_{n+1}` 的像、以及 `B_r` 作为来向微分像的原像的刻画
在文件末尾。 -/

/-- 提升微分：从循环子对象的底层对象出发，
`Z_n → E_r^k → E_r^{k+deg}`，其中 `n = (r - r₀).toNat`。
这就是 AIM 论文的 `d̃_r : Z_{r-1} → E_2/B_{r-1}`（在内部重编号下）。 -/
noncomputable def SpectralSequence.liftedD
    (E : SpectralSequence C ι) (r : ℤ) (k : ι) :
    Subobject.underlying.obj ((E.ssData k).Z ↑(r - E.r₀).toNat) ⟶
      E.Page r (k + E.diffDeg r) :=
  (E.ssData k).pageπ _ ≫ E.d r k

/-- 提升微分在边界子对象上消失：`B_n → Z_n → E_r^{k+deg}` 为零。
这给出它诱导回页微分 `d_r` 的合法性（`d_r` 本就是商上的映射）。 -/
theorem SpectralSequence.liftedD_vanishes_on_boundaries
    (E : SpectralSequence C ι) (r : ℤ) (k : ι) :
    Subobject.ofLE ((E.ssData k).B ↑(r - E.r₀).toNat)
        ((E.ssData k).Z ↑(r - E.r₀).toNat) ((E.ssData k).B_le_Z _) ≫
      E.liftedD r k = 0 := by
  change Subobject.ofLE ((E.ssData k).B ↑(r - E.r₀).toNat)
      ((E.ssData k).Z ↑(r - E.r₀).toNat) ((E.ssData k).B_le_Z _) ≫
    ((E.ssData k).pageπ _ ≫ E.d r k) = 0
  rw [cokernel.condition_assoc, zero_comp]

/-- 提升微分的核（作为循环子对象 `Z_n` 的子对象，
`n = (r - r₀).toNat`）恰为下一层循环 `Z_{n+1} ↪ Z_n` 的像。

数学内容：`liftedD = pageπ ≫ d r k`，`pageπ : Z_n → Z_n/B_n` 满射，
其核为 `B_n`；由 `Z_succ`，`ker(d_r) = image(Z_{n+1} → Z_n/B_n)`。
满射的原像公式给出 `ker(liftedD) = image(Z_{n+1} ↪ Z_n) ⊔ B_n`，
而 `B_n ≤ B_{n+1} ≤ Z_{n+1}`，故并塌陷为 `image(Z_{n+1} ↪ Z_n)`。

证明路线：令 `P = B_n`、`Q = Z_{n+1}`、`R = Z_n`。
由 `Z_succ` 以及满射不改变后接态射的像，得到
`ker(d_r) = image(Q/P → R/P)`，因而 `d_r` 唯一下降为单射
`coker(Q/P → R/P) → E_r`。再用第三同构定理把这个余核识别为
`R/Q`，于是 `liftedD` 的核等于商映射 `R → R/Q` 的核；
最后由余核正合性把该核识别为 `Q ↪ R` 的像。 -/
theorem SpectralSequence.liftedD_kernel
    (E : SpectralSequence C ι) (r : ℤ) (k : ι) (hr : E.r₀ ≤ r) :
    kernelSubobject (E.liftedD r k) =
      imageSubobject
        (Subobject.ofLE ((E.ssData k).Z ↑((r + 1 - E.r₀).toNat))
          ((E.ssData k).Z ↑(r - E.r₀).toNat)
          ((E.ssData k).Z_anti (by
            have : (r + 1 - E.r₀).toNat = (r - E.r₀).toNat + 1 := by omega
            rw [this]
            exact_mod_cast Nat.le_succ _))) := by
  let n := (r - E.r₀).toNat
  have hn : (r + 1 - E.r₀).toNat = n + 1 := by
    dsimp only [n]
    omega
  let D := E.ssData k
  let P := D.B (n : WithTop ℕ)
  let Q₀ := D.Z ((r + 1 - E.r₀).toNat : WithTop ℕ)
  let R := D.Z (n : WithTop ℕ)
  have hlevel : (n : WithTop ℕ) ≤ ((r + 1 - E.r₀).toNat : WithTop ℕ) := by
    rw [hn]
    exact_mod_cast Nat.le_succ n
  have hPQ₀ : P ≤ Q₀ := le_trans
    (D.B_mono hlevel) (D.B_le_Z _)
  have hQR₀ : Q₀ ≤ R := D.Z_anti hlevel
  have hPR : P ≤ R := D.B_le_Z _
  change kernelSubobject (E.liftedD r k) =
    imageSubobject (Subobject.ofLE Q₀ R hQR₀)
  have hQ : Q₀ = D.Z ((n + 1 : ℕ) : WithTop ℕ) := by
    dsimp only [Q₀, D, n]
    rw [hn]
  let Q := D.Z ((n + 1 : ℕ) : WithTop ℕ)
  have hPQ : P ≤ Q := by
    dsimp only [Q]
    rw [← hQ]
    exact hPQ₀
  have hQR : Q ≤ R := by
    dsimp only [Q]
    rw [← hQ]
    exact hQR₀
  have image_ofLE_eq_of_eq : ∀ (S T : Subobject D.V)
      (hS : S ≤ R) (hT : T ≤ R), S = T →
        imageSubobject (Subobject.ofLE S R hS) =
          imageSubobject (Subobject.ofLE T R hT) := by
    intro S T hS hT hST
    subst T
    rfl
  have htarget : imageSubobject (Subobject.ofLE Q₀ R hQR₀) =
      imageSubobject (Subobject.ofLE Q R hQR) :=
    image_ofLE_eq_of_eq Q₀ Q hQR₀ hQR hQ
  rw [htarget]
  let b := Subobject.ofLE P Q hPQ
  let j := Subobject.ofLE Q R hQR
  let a := Subobject.ofLE P R hPR
  let p := cokernel.π a
  let i := Subobject.cokernelMap_ofLE P Q R hPQ hQR hPR
  have hfactor : j ≫ p = cokernel.π b ≫ i := by
    simp only [j, p, b, i, a, Subobject.cokernelMap_ofLE,
      cokernel.π_desc]
  have image_epi_comp : ∀ {X₁ X₂ X₃ : C} (e : X₁ ⟶ X₂) [Epi e]
      (f : X₂ ⟶ X₃), imageSubobject (e ≫ f) = imageSubobject f := by
    intro X₁ X₂ X₃ e _ f
    have hle := imageSubobject_comp_le e f
    haveI : Epi (Subobject.ofLE _ _ hle) :=
      imageSubobject_comp_le_epi_of_epi e f
    haveI : IsIso (Subobject.ofLE _ _ hle) := isIso_of_mono_of_epi _
    exact le_antisymm hle (Subobject.le_of_comm
      (inv (Subobject.ofLE _ _ hle)) (by
        rw [IsIso.inv_comp_eq]
        exact (Subobject.ofLE_arrow hle).symm))
  have hker : kernelSubobject (E.d r k) = imageSubobject i := by
    have hZ := E.Z_succ r k hr
    change kernelSubobject (E.d r k) = imageSubobject (j ≫ p) at hZ
    rw [hZ, hfactor, image_epi_comp]
  have wi : i ≫ E.d r k = 0 := by
    have hle : imageSubobject i ≤ kernelSubobject (E.d r k) := by
      rw [hker]
    rw [← imageSubobject_arrow_comp i, Category.assoc,
      show (imageSubobject i).arrow =
          Subobject.ofLE (imageSubobject i) (kernelSubobject (E.d r k)) hle ≫
            (kernelSubobject (E.d r k)).arrow
        from (Subobject.ofLE_arrow hle).symm,
      Category.assoc, kernelSubobject_arrow_comp, comp_zero, comp_zero]
  let desc := cokernel.desc i (E.d r k) wi
  haveI desc_mono : Mono desc := by
    open CategoryTheory.Abelian.Pseudoelement in
      refine mono_of_zero_of_map_zero desc fun x hx => ?_
      obtain ⟨y, hy⟩ := pseudo_surjective_of_epi (cokernel.π i) x
      rw [← hy] at hx ⊢
      have hyd : pseudoApply (E.d r k) y = 0 := by
        rw [← cokernel.π_desc i (E.d r k) wi,
          CategoryTheory.Abelian.Pseudoelement.comp_apply]
        exact hx
      have hexact : (ShortComplex.mk i (E.d r k) wi).Exact := by
        rw [ShortComplex.exact_iff_image_eq_kernel]
        exact hker.symm
      obtain ⟨z, hz⟩ := pseudo_exact_of_exact hexact y hyd
      rw [← hz, ← CategoryTheory.Abelian.Pseudoelement.comp_apply,
        cokernel.condition, zero_apply]
  let e := Subobject.thirdIso P Q R hPQ hQR hPR
  let q := Subobject.cokernelDesc_ofLE P Q R hPQ hQR hPR
  let m := e.inv ≫ desc
  haveI : Mono m := mono_comp _ _
  have hπe : cokernel.π i ≫ e.hom = q := by
    exact cokernel.π_desc _ _ _
  have hpq : p ≫ q = cokernel.π j := by
    dsimp only [p, q, a, j, Subobject.cokernelDesc_ofLE]
    rw [cokernel.π_desc]
  have hquot : cokernel.π j ≫ m = p ≫ E.d r k := by
    calc
      cokernel.π j ≫ m = (p ≫ q) ≫ (e.inv ≫ desc) := by
        rw [hpq]
      _ = p ≫ ((q ≫ e.inv) ≫ desc) := by
        simp only [Category.assoc]
      _ = p ≫ ((cokernel.π i ≫ e.hom ≫ e.inv) ≫ desc) := by
        rw [← hπe]
        simp only [Category.assoc]
      _ = p ≫ (cokernel.π i ≫ desc) := by
        simp only [Iso.hom_inv_id, Category.comp_id]
      _ = p ≫ E.d r k := by
        rw [cokernel.π_desc]
  change kernelSubobject (p ≫ E.d r k) = imageSubobject j
  rw [← hquot, kernelSubobject_comp_mono]
  have hexact := ShortComplex.exact_cokernel j
  rw [ShortComplex.exact_iff_image_eq_kernel] at hexact
  exact hexact.symm

/-- 来向提升微分在目标侧的像刻画（`B_succ` 的直接重述）：
`liftedD r k` 的像（作为页 `E_r^{k+deg}` 的子对象）等于
`B_{n+1} ↪ Z_n → Z_n/B_n` 的像。

数学内容：`liftedD = pageπ ≫ d r k`，`pageπ` 满，故
`image(liftedD) = image(d_r)`，而 `B_succ` 给出
`image(d_r) = image(ofLE(B_{n+1},Z_n) ≫ pageπ)`。
这给出"B_r 是来向微分像的原像"的页内形式（缺口 1 的第三条）。

证明路线：
1. `hle : image(pageπ ≫ d) ≤ image(d)` 为 `imageSubobject_comp_le`；
2. `hge : image(d) ≤ image(pageπ ≫ d)`：`pageπ` 满 ⇒ 连接映射
   `ofLE (imageSubobject_comp_le …)` 满且单，故为同构，
   其逆给出反向 ≤（`Subobject.le_of_comm`）；
3. 与 `B_succ` 对接时把 `(r+1-r₀).toNat` 改写为 `(r-r₀).toNat + 1`。 -/
theorem SpectralSequence.liftedD_image_eq_boundary_image
    (E : SpectralSequence C ι) (r : ℤ) (k : ι) (hr : E.r₀ ≤ r) :
    imageSubobject (E.liftedD r k) =
      imageSubobject
        (Subobject.ofLE ((E.ssData (k + E.diffDeg r)).B
            ↑((r + 1 - E.r₀).toNat))
          ((E.ssData (k + E.diffDeg r)).Z ↑(r - E.r₀).toNat)
          (le_trans ((E.ssData (k + E.diffDeg r)).B_le_Z _)
            ((E.ssData (k + E.diffDeg r)).Z_anti (by
              have : (r + 1 - E.r₀).toNat = (r - E.r₀).toNat + 1 := by omega
              rw [this]
              exact_mod_cast Nat.le_succ _))) ≫
          (E.ssData (k + E.diffDeg r)).pageπ ↑(r - E.r₀).toNat) := by
  -- 换参路线：先转 page 目标对象（项级 ▸），再把 B ↑(r+1-r₀).toNat
  -- 换成 B ↑(n+1)；hsub 只出现在 ofLE 的第一个参数位（证明项不透出）。
  have htarget : E.Page r (k + E.diffDeg r) =
      (E.ssData (k + E.diffDeg r)).page ↑(r - E.r₀).toNat := rfl
  have hsub : ((E.ssData (k + E.diffDeg r)).B ↑(r + 1 - E.r₀).toNat : Subobject _) =
      (E.ssData (k + E.diffDeg r)).B ↑((r - E.r₀).toNat + 1) := by
    rw [show (r + 1 - E.r₀).toNat = (r - E.r₀).toNat + 1 from by omega]
  -- 在等式层面用 ▸ 转换：▸ 只重写类型层，子对象值不变
  have key : imageSubobject (E.liftedD r k) =
      imageSubobject (Subobject.ofLE ((E.ssData (k + E.diffDeg r)).B
          ↑((r - E.r₀).toNat + 1))
        ((E.ssData (k + E.diffDeg r)).Z ↑(r - E.r₀).toNat)
        (le_trans ((E.ssData (k + E.diffDeg r)).B_le_Z _)
          ((E.ssData (k + E.diffDeg r)).Z_anti (by
            exact_mod_cast Nat.le_succ _))) ≫
        (E.ssData (k + E.diffDeg r)).pageπ ↑(r - E.r₀).toNat) := by
    change imageSubobject ((E.ssData k).pageπ ↑(r - E.r₀).toNat ≫ E.d r k) = _
    have hle : imageSubobject ((E.ssData k).pageπ ↑(r - E.r₀).toNat ≫ E.d r k) ≤
        imageSubobject (E.d r k) := imageSubobject_comp_le _ _
    have hge : imageSubobject (E.d r k) ≤
        imageSubobject ((E.ssData k).pageπ ↑(r - E.r₀).toNat ≫ E.d r k) := by
      haveI : IsIso (Subobject.ofLE _ _ (imageSubobject_comp_le
        ((E.ssData k).pageπ ↑(r - E.r₀).toNat) (E.d r k))) :=
        isIso_of_mono_of_epi _
      exact Subobject.le_of_comm (inv (Subobject.ofLE _ _
        (imageSubobject_comp_le ((E.ssData k).pageπ ↑(r - E.r₀).toNat)
          (E.d r k)))) (by simp [Subobject.ofLE_arrow])
    rw [le_antisymm hle hge]
    exact E.B_succ r k hr
  -- key 的 RHS 与目标的 RHS 经 hsub 相等：先把 hsub 提升为
  -- 复合态射层的等式（源对象经 eqToHom hsub 转换），再拼接。
  -- 核心：ofLE 的箭头由 Subobject.arrow 决定，hsub 是子对象等式，
  -- arrow_congr 给出 eqToHom (obj hsub) ≫ (B').arrow = B.arrow，
  -- 与 ofLE_arrow 结合得 ofLE 层的等式。
  have h2 : Subobject.ofLE ((E.ssData (k + E.diffDeg r)).B ↑(r + 1 - E.r₀).toNat)
      ((E.ssData (k + E.diffDeg r)).Z ↑(r - E.r₀).toNat)
      (le_trans ((E.ssData (k + E.diffDeg r)).B_le_Z _)
        ((E.ssData (k + E.diffDeg r)).Z_anti (by
          have : (r + 1 - E.r₀).toNat = (r - E.r₀).toNat + 1 := by omega
          rw [this]
          exact_mod_cast Nat.le_succ _))) =
    eqToHom (congrArg Subobject.underlying.obj hsub) ≫
      Subobject.ofLE ((E.ssData (k + E.diffDeg r)).B ↑((r - E.r₀).toNat + 1))
        ((E.ssData (k + E.diffDeg r)).Z ↑(r - E.r₀).toNat)
        (le_trans ((E.ssData (k + E.diffDeg r)).B_le_Z _)
          ((E.ssData (k + E.diffDeg r)).Z_anti (by
            exact_mod_cast Nat.le_succ _))) := by
    -- 消去 ofLE：用 ofLE_arrow 把两边映到 Z.arrow 后的箭头比较
    apply (cancel_mono ((E.ssData (k + E.diffDeg r)).Z
      ↑(r - E.r₀).toNat).arrow).mp
    rw [Subobject.ofLE_arrow]
    rw [Category.assoc, Subobject.ofLE_arrow]
    exact (Subobject.arrow_congr _ _ hsub).symm
  have h1 : Subobject.ofLE ((E.ssData (k + E.diffDeg r)).B ↑(r + 1 - E.r₀).toNat)
      ((E.ssData (k + E.diffDeg r)).Z ↑(r - E.r₀).toNat)
      (le_trans ((E.ssData (k + E.diffDeg r)).B_le_Z _)
        ((E.ssData (k + E.diffDeg r)).Z_anti (by
          have : (r + 1 - E.r₀).toNat = (r - E.r₀).toNat + 1 := by omega
          rw [this]
          exact_mod_cast Nat.le_succ _))) ≫
      (E.ssData (k + E.diffDeg r)).pageπ ↑(r - E.r₀).toNat =
    eqToHom (congrArg Subobject.underlying.obj hsub) ≫
      (Subobject.ofLE ((E.ssData (k + E.diffDeg r)).B ↑((r - E.r₀).toNat + 1))
        ((E.ssData (k + E.diffDeg r)).Z ↑(r - E.r₀).toNat)
        (le_trans ((E.ssData (k + E.diffDeg r)).B_le_Z _)
          ((E.ssData (k + E.diffDeg r)).Z_anti (by
            exact_mod_cast Nat.le_succ _))) ≫
        (E.ssData (k + E.diffDeg r)).pageπ ↑(r - E.r₀).toNat) := by
    rw [h2, Category.assoc]
  have hcong : imageSubobject (Subobject.ofLE
        ((E.ssData (k + E.diffDeg r)).B ↑(r + 1 - E.r₀).toNat)
        ((E.ssData (k + E.diffDeg r)).Z ↑(r - E.r₀).toNat)
        (le_trans ((E.ssData (k + E.diffDeg r)).B_le_Z _)
          ((E.ssData (k + E.diffDeg r)).Z_anti (by
            have : (r + 1 - E.r₀).toNat = (r - E.r₀).toNat + 1 := by omega
            rw [this]
            exact_mod_cast Nat.le_succ _))) ≫
        (E.ssData (k + E.diffDeg r)).pageπ ↑(r - E.r₀).toNat) =
      imageSubobject (Subobject.ofLE ((E.ssData (k + E.diffDeg r)).B
          ↑((r - E.r₀).toNat + 1))
        ((E.ssData (k + E.diffDeg r)).Z ↑(r - E.r₀).toNat)
        (le_trans ((E.ssData (k + E.diffDeg r)).B_le_Z _)
          ((E.ssData (k + E.diffDeg r)).Z_anti (by
            exact_mod_cast Nat.le_succ _))) ≫
        (E.ssData (k + E.diffDeg r)).pageπ ↑(r - E.r₀).toNat) := by
    rw [h1, imageSubobject_iso_comp]
  exact key.trans hcong.symm

end KIPBase.SpectralSequence
