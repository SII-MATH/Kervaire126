/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import KIPBase.SpectralSequence.UnboundedCommutativity

/-!
# 扩张谱序列与极限对象上的正合性

本文件证明 blueprint 中“中间正合使永久循环成为边缘”的命题。正合性只在
一个固定的极限次数 `τ` 上要求，而不是在所有次数上要求。
-/

namespace KIPBase.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v w

set_option linter.dupNamespace false

variable {C : Type u} [Category.{v} C] [Abelian C]
variable [LocallySmall.{u} C] [WellPowered.{u} C]
variable [HasWidePullbacks.{u} C] [HasCoproducts.{u} C]

/-- 两个可复合的收敛谱序列态射在指定极限次数 `τ` 的 abutment 上正合。
该谓词不要求任何其他次数上的正合性。 -/
def AbutmentExactAt
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {ω' : Type w}
    (V₁ V₂ V₃ : ConvergingSS C ω ω')
    (f : V₁ ⟶ V₂) (g : V₂ ⟶ V₃) (τ : ω') : Prop :=
  ∃ hfg : f.aMap τ ≫ g.aMap τ = 0,
    (ShortComplex.mk (f.aMap τ) (g.aMap τ) hfg).Exact

/-- 一个原始 `E∞` 类形式上属于 `f`-ESS 的无限循环子对象 `Z∞`。在弱收敛
下，这个纯谱序列条件本身不保证存在一个相容的 abutment 代表元。 -/
def ESSFormalPermanentCycle
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {ω' : Type w}
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    (f : ConvergenceMorphism conv₁ conv₂) (τ : ω') (s : ℤ)
    {T : C}
    (y : T ⟶ (unboundedExtensionSSData f τ (s, 1)).V) : Prop :=
  ((unboundedExtensionSSData f τ (s, 1)).Z ⊤).Factors y

/-- `f`-ESS 的相容永久循环：存在一个检测 `y` 的固定 abutment 代表元，
其在目标中的像落在每一个过滤层中。真正的 Hausdorff 条件正好把这个像
杀掉。这个相容性不能仅由弱收敛下的形式 `Z∞` 条件推出。 -/
def ESSPermanentCycle
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {ω' : Type w}
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    (f : ConvergenceMorphism conv₁ conv₂) (τ : ω') (s : ℤ)
    {T : C}
    (y : T ⟶ (unboundedExtensionSSData f τ (s, 1)).V) : Prop :=
  ∃ yl : T ⟶ Subobject.underlying.obj (F₁.F s τ),
    UnboundedExtensionIsLift f τ s 1 yl y ∧
    ∀ v : ℤ, (F₂.F v τ).Factors
      ((yl ≫ (F₁.F s τ).arrow) ≫ f.aMap τ)

/-- 一个永久循环的 abutment 代表元数据：代表元检测给定的原始 `E∞`
类，并且被 `f.aMap τ` 杀掉。 -/
def ESSPermanentRepresentative
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {ω' : Type w}
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    (f : ConvergenceMorphism conv₁ conv₂) (τ : ω') (s : ℤ)
    {T : C}
    (y : T ⟶ (unboundedExtensionSSData f τ (s, 1)).V) : Prop :=
  ∃ yl : T ⟶ Subobject.underlying.obj (F₁.F s τ),
    UnboundedExtensionIsLift f τ s 1 yl y ∧
    (yl ≫ (F₁.F s τ).arrow) ≫ f.aMap τ = 0

/-- 投射广义元素若在无界 ESS 中永久，则可选取一个代表它的过滤提升，
而且该提升在极限对象中的像被 ESS 所对应的态射杀掉。 -/
theorem unbounded_lift_of_permanentRepresentative
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {ω' : Type w}
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    (f : ConvergenceMorphism conv₁ conv₂) (τ : ω') (s : ℤ)
    {T : C}
    {y : T ⟶ (unboundedExtensionSSData f τ (s, 1)).V}
    (hy : ESSPermanentRepresentative f τ s y) :
    ∃ yl : T ⟶ Subobject.underlying.obj (F₁.F s τ),
      UnboundedExtensionIsLift f τ s 1 yl y ∧
    (yl ≫ (F₁.F s τ).arrow) ≫ f.aMap τ = 0 := by
  exact hy

/-- 若目标过滤在固定次数 `τ` 上真正 Hausdorff，则相容永久循环的固定
代表元在目标中的像为零，因而给出一个被 abutment 映射杀掉的代表元。 -/
theorem permanentRepresentative_of_permanentCycle
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {ω' : Type w}
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    (f : ConvergenceMorphism conv₁ conv₂) (τ : ω') (s : ℤ)
    {T : C}
    {y : T ⟶ (unboundedExtensionSSData f τ (s, 1)).V}
    (hHausdorff : F₂.IsHausdorffAt τ)
    (hy : ESSPermanentCycle f τ s y) :
    ESSPermanentRepresentative f τ s y := by
  classical
  rcases hy with ⟨yl, hyl, hdeep⟩
  let z := (yl ≫ (F₁.F s τ).arrow) ≫ f.aMap τ
  have himage_le (v : ℤ) : imageSubobject z ≤ F₂.F v τ := by
    rcases (Subobject.factors_iff _ _).1 (hdeep v) with ⟨zv, hzv⟩
    exact imageSubobject_le z zv hzv
  have himage_bot : imageSubobject z = ⊥ :=
    hHausdorff (imageSubobject z) himage_le
  have hzfac : (imageSubobject z).Factors z := by
    simpa using imageSubobject_factors_comp_self (f := z) (𝟙 T)
  have hz : z = 0 := by
    rw [himage_bot, Subobject.bot_factors_iff_zero] at hzfac
    exact hzfac
  exact ⟨yl, hyl, hz⟩

/-- 固定一个极限次数 `τ`。若两个可复合的收敛谱序列态射在该次数的
abutment 上正合，则中间谱序列的每个投射永久 `g`-ESS 循环都被某个
`f`-ESS 微分击中。这里既不假设 `f.aMap τ` 单射，也不假设
`g.aMap τ` 满射。 -/
theorem ess_boundary_of_exact_at_abutment_of_representative
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {ω' : Type w}
    (V₁ V₂ V₃ : ConvergingSS C ω ω')
    (f : V₁ ⟶ V₂) (g : V₂ ⟶ V₃)
    (τ : ω')
    (hexact : AbutmentExactAt V₁ V₂ V₃ f g τ)
    (hboundedBelow : ∃ u₀ : ℤ, V₁.F.F u₀ τ = ⊤)
    (s : ℤ) {T : C} [Projective T]
    (y : T ⟶ (V₂.E.ssData
      (V₂.conv.reindexEquiv.symm (s, τ))).eInfty)
    (hy : ESSPermanentRepresentative g τ s y) :
    ∃ (u : ℤ) (_hu : u ≤ s)
      (x : T ⟶ (V₁.E.ssData
        (V₁.conv.reindexEquiv.symm (u, τ))).eInfty),
      DifferentialRelation (ExtensionSpectralSequence f τ) (s - u) (u, 1) x
        (Eq.mpr (congrArg (fun X : C => T ⟶ X)
          (show ((ExtensionSpectralSequence f τ).ssData
              ((u, 1) + (ExtensionSpectralSequence f τ).diffDeg (s - u))).V =
            (unboundedExtensionSSData f τ (s, 0)).V by
              have hus : u + (s - u) = s := by omega
              rw [ExtensionSpectralSequence_diffDeg]
              simp only [Prod.mk_add_mk, hus]
              rfl)) y) := by
  classical
  rcases hexact with ⟨hfg, hex⟩
  obtain ⟨yl, hyl, hyg⟩ :=
    unbounded_lift_of_permanentRepresentative g τ s hy
  have hylf : UnboundedExtensionIsLift f τ s 0 yl y :=
    by
      unfold UnboundedExtensionIsLift at hyl ⊢
      rw [unboundedExtensionVComplexIso_target_source_hom_eq f g τ s]
      exact hyl
  let yA : T ⟶ V₂.A τ := yl ≫ (V₂.F.F s τ).arrow
  have hyA_zero : yA ≫ g.aMap τ = 0 := by
    exact hyg
  have hker : (kernelSubobject (g.aMap τ)).Factors yA :=
    kernelSubobject_factors (g.aMap τ) yA hyA_zero
  have himage : imageSubobject (f.aMap τ) = kernelSubobject (g.aMap τ) :=
    (ShortComplex.exact_iff_image_eq_kernel _).1 hex
  have himageFactor : (imageSubobject (f.aMap τ)).Factors yA := by
    rw [himage]
    exact hker
  let yI := (imageSubobject (f.aMap τ)).factorThru yA himageFactor
  let xA := Projective.factorThru yI
    (factorThruImageSubobject (f.aMap τ))
  have hxA : xA ≫ f.aMap τ = yA := by
    calc
      xA ≫ f.aMap τ =
          (xA ≫ factorThruImageSubobject (f.aMap τ)) ≫
            (imageSubobject (f.aMap τ)).arrow := by
              rw [Category.assoc, imageSubobject_arrow_comp]
      _ = yI ≫ (imageSubobject (f.aMap τ)).arrow := by
            rw [Projective.factorThru_comp]
      _ = yA := (imageSubobject (f.aMap τ)).factorThru_arrow yA himageFactor
  rcases hboundedBelow with ⟨u₀, hu₀⟩
  let u := min u₀ s
  have hu : u ≤ s := min_le_right _ _
  have hutop : V₁.F.F u τ = ⊤ := by
    apply top_unique
    have hle : V₁.F.F u₀ τ ≤ V₁.F.F u τ :=
      V₁.F.mono_of_le (min_le_left _ _) τ
    rwa [hu₀] at hle
  letI : IsIso (V₁.F.F u τ).arrow :=
    (Subobject.isIso_arrow_iff_eq_top _).2 hutop
  let xl : T ⟶ Subobject.underlying.obj (V₁.F.F u τ) :=
    xA ≫ inv (V₁.F.F u τ).arrow
  have hxl : xl ≫ (V₁.F.F u τ).arrow = xA := by
    dsimp only [xl]
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  let FC := unboundedUnderlyingComplex f τ
  let x : T ⟶ (unboundedExtensionSSData f τ (u, 1)).V :=
    UnboundedExtensionClass f τ u 1
      (xl ≫ FC.filToAssocGraded u 1)
  have hxlift : UnboundedExtensionIsLift f τ u 1 xl x := by
    dsimp only [x]
    unfold UnboundedExtensionIsLift UnboundedExtensionClass
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl
  have ha : xl ≫ (FC.fil u 1).arrow ≫ f.aMap τ =
      yl ≫ (FC.fil s 0).arrow := by
    change xl ≫ (V₁.F.F u τ).arrow ≫ f.aMap τ =
      yl ≫ (V₂.F.F s τ).arrow
    calc
      xl ≫ (V₁.F.F u τ).arrow ≫ f.aMap τ =
          xA ≫ f.aMap τ := by rw [← Category.assoc, hxl]
      _ = yA := hxA
      _ = yl ≫ (V₂.F.F s τ).arrow := rfl
  refine ⟨u, hu, x, ?_⟩
  exact unboundedDifferentialRelation_of_ambient_map f τ
    (s - u) (by omega) u s (by omega) xl yl hxlift hylf ha

/-- 固定一个极限次数 `τ`。若 `f`、`g` 的 abutment 映射在该次数正合，
源过滤在该次数有一个等于整个对象的层，且 `g` 的目标过滤在该次数真正
Hausdorff，那么中间谱序列的每个投射相容永久 `g`-ESS 循环都被某个
`f`-ESS 微分击中。所有三个附加条件都只针对指定的 `τ`。 -/
theorem ess_boundary_of_exact_at_abutment
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {ω' : Type w}
    (V₁ V₂ V₃ : ConvergingSS C ω ω')
    (f : V₁ ⟶ V₂) (g : V₂ ⟶ V₃)
    (τ : ω')
    (hexact : AbutmentExactAt V₁ V₂ V₃ f g τ)
    (hboundedBelow : ∃ u₀ : ℤ, V₁.F.F u₀ τ = ⊤)
    (hHausdorff : V₃.F.IsHausdorffAt τ)
    (s : ℤ) {T : C} [Projective T]
    (y : T ⟶ (V₂.E.ssData
      (V₂.conv.reindexEquiv.symm (s, τ))).eInfty)
    (hy : ESSPermanentCycle g τ s y) :
    ∃ (u : ℤ) (_hu : u ≤ s)
      (x : T ⟶ (V₁.E.ssData
        (V₁.conv.reindexEquiv.symm (u, τ))).eInfty),
      DifferentialRelation (ExtensionSpectralSequence f τ) (s - u) (u, 1) x
        (Eq.mpr (congrArg (fun X : C => T ⟶ X)
          (show ((ExtensionSpectralSequence f τ).ssData
              ((u, 1) + (ExtensionSpectralSequence f τ).diffDeg (s - u))).V =
            (unboundedExtensionSSData f τ (s, 0)).V by
              have hus : u + (s - u) = s := by omega
              rw [ExtensionSpectralSequence_diffDeg]
              simp only [Prod.mk_add_mk, hus]
              rfl)) y) := by
  apply ess_boundary_of_exact_at_abutment_of_representative
    V₁ V₂ V₃ f g τ hexact hboundedBelow s y
  exact permanentRepresentative_of_permanentCycle g τ s hHausdorff hy

end KIPBase.SpectralSequence
