/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Bounded extension spectral sequence: basic convergence, filtered crossing.
Reference: extension.tex (wangguozhen-fudan/spectral-sequence-notes)
-/

import KIPBase.SpectralSequence.Basic
import KIPBase.SpectralSequence.Convergence
import KIPBase.SpectralSequence.FilteredComplex
import KIPBase.SpectralSequence.Crossing

universe u v w

namespace KIPBase.SpectralSequence

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [Abelian C]

/-! ### Two-term complex helpers

The extension spectral sequence is built from a two-term filtered complex
`A₁(t) →[aMap t] A₂(t)` for each stem degree `t`. These helpers define the
graded object, differential, and filtration for such a complex. -/

/-- The graded object for a two-term complex: `A(1) = X₁`, `A(0) = X₂`,
    `A(k) = 0` for all other `k`. The zero object is `⊥_ C` (initial object
    in an abelian category). -/
noncomputable def twoTermObj (X₁ X₂ : C) : ℤ → C := fun k =>
  if k = 1 then X₁ else if k = 0 then X₂ else ⊥_ C

@[simp] lemma twoTermObj_one (X₁ X₂ : C) : twoTermObj X₁ X₂ 1 = X₁ := by
  simp [twoTermObj]

@[simp] lemma twoTermObj_zero' (X₁ X₂ : C) : twoTermObj X₁ X₂ 0 = X₂ := by
  simp [twoTermObj]

lemma twoTermObj_other (X₁ X₂ : C) (k : ℤ) (h₁ : k ≠ 1) (h₀ : k ≠ 0) :
    twoTermObj X₁ X₂ k = ⊥_ C := by
  simp [twoTermObj, h₁, h₀]

/-- The differential for the two-term complex: `d(1) = f : X₁ ⟶ X₂`,
    `d(k) = 0` for `k ≠ 1`. Uses `eqToHom` to bridge the definitional
    gap between `twoTermObj` at specific integers. -/
noncomputable def twoTermDiff (X₁ X₂ : C) (f : X₁ ⟶ X₂) :
    (k : ℤ) → twoTermObj X₁ X₂ k ⟶ twoTermObj X₁ X₂ (k - 1) := fun k =>
  if h : k = 1 then
    eqToHom (show twoTermObj X₁ X₂ k = X₁ by simp [twoTermObj, h]) ≫ f ≫
      eqToHom (show X₂ = twoTermObj X₁ X₂ (k - 1) by simp [twoTermObj, h])
  else 0

theorem twoTermDiff_sq (X₁ X₂ : C) (f : X₁ ⟶ X₂) (k : ℤ) :
    twoTermDiff X₁ X₂ f k ≫ twoTermDiff X₁ X₂ f (k - 1) = 0 := by
  simp only [twoTermDiff]
  by_cases h : k = 1
  · subst h; simp
  · simp [h]

/-- The filtration for the two-term complex: at `k = 1` use `fil₁`,
    at `k = 0` use `fil₂`, at all other `k` use `⊤` (which equals `⊥`
    on the zero object). -/
noncomputable def twoTermFil {X₁ X₂ : C}
    (fil₁ : ℤ → Subobject X₁) (fil₂ : ℤ → Subobject X₂) :
    ℤ → (k : ℤ) → Subobject (twoTermObj X₁ X₂ k) := fun s k =>
  if h₁ : k = 1 then h₁ ▸ fil₁ s
  else if h₀ : k = 0 then h₀ ▸ fil₂ s
  else ⊤

@[simp] lemma twoTermFil_one {X₁ X₂ : C}
    (fil₁ : ℤ → Subobject X₁) (fil₂ : ℤ → Subobject X₂) (s : ℤ) :
    twoTermFil fil₁ fil₂ s 1 = fil₁ s := by simp [twoTermFil]

@[simp] lemma twoTermFil_zero' {X₁ X₂ : C}
    (fil₁ : ℤ → Subobject X₁) (fil₂ : ℤ → Subobject X₂) (s : ℤ) :
    twoTermFil fil₁ fil₂ s 0 = fil₂ s := by simp [twoTermFil]

private lemma subobject_eq_bot_of_isZero {X : C} (hX : IsZero X) (P : Subobject X) : P = ⊥ := by
  have hP_zero : IsZero (Subobject.underlying.obj P) := hX.of_mono P.arrow
  apply le_antisymm
  · apply Subobject.le_of_comm (hP_zero.to_ _)
    apply hX.eq_of_tgt
  · exact bot_le

private lemma subobject_top_eq_bot_of_isInitial :
    (⊤ : Subobject (⊥_ C)) = ⊥ :=
  subobject_eq_bot_of_isZero (by apply IsInitial.isZero; exact initialIsInitial) ⊤

/-! ### Underlying filtered complex

Given a convergence morphism `cm : ConvergenceMorphism conv₁ conv₂` with
`cm.aMap : A₁ k' ⟶ A₂ k'`, for each stem degree `t : ω'` we build a
`FilteredComplex C` whose underlying chain complex is the two-term complex
`A₁(t) →[cm.aMap t] A₂(t)`, with filtration inherited from `F₁` and `F₂`. -/

variable {ω' : Type w}

/-- The two-term filtered complex `A₁(t) → A₂(t)` at stem degree `t`,
    with filtration inherited from `F₁` and `F₂`. -/
noncomputable def underlyingComplex
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    (aMap : ∀ k', A₁ k' ⟶ A₂ k')
    (hcompat : ∀ (s : ℤ) (k' : ω'),
      ∃ (φ : Subobject.underlying.obj (F₁.F s k') ⟶
             Subobject.underlying.obj (F₂.F s k')),
        φ ≫ (F₂.F s k').arrow = (F₁.F s k').arrow ≫ aMap k')
    (t : ω') : FilteredComplex C where
  A := twoTermObj (A₁ t) (A₂ t)
  d := twoTermDiff (A₁ t) (A₂ t) (aMap t)
  d_comp_d := twoTermDiff_sq (A₁ t) (A₂ t) (aMap t)
  fil := twoTermFil (fun s => F₁.F s t) (fun s => F₂.F s t)
  fil_anti := fun s k => by
    simp only [twoTermFil]
    by_cases h₁ : k = 1
    · subst h₁; simp only [↓reduceDIte]; exact F₁.mono s t
    · by_cases h₀ : k = 0
      · subst h₀; simp only [↓reduceDIte, h₁]; exact F₂.mono s t
      · simp [h₁, h₀]
  d_preserves_fil := fun s k => by
    by_cases h : k = 1
    · subst h
      obtain ⟨φ, hφ⟩ := hcompat s t
      have h1 : twoTermFil (fun s => F₁.F s t) (fun s => F₂.F s t) s 1 = F₁.F s t :=
        by simp [twoTermFil]
      have h0 : twoTermFil (fun s => F₁.F s t) (fun s => F₂.F s t) s (1 - 1) = F₂.F s t :=
        by simp [twoTermFil]
      have harr0 : (twoTermFil (fun s => F₁.F s t) (fun s => F₂.F s t) s (1 - 1)).arrow =
          eqToHom (by simp [twoTermFil, twoTermObj]) ≫ (F₂.F s t).arrow := by
        simp [twoTermFil, twoTermObj]
      have harr1 : (twoTermFil (fun s => F₁.F s t) (fun s => F₂.F s t) s 1).arrow =
          eqToHom (by simp [twoTermFil, twoTermObj]) ≫ (F₁.F s t).arrow := by
        simp [twoTermFil, twoTermObj]
      exact ⟨h1 ▸ h0 ▸ φ, by
        simp only [twoTermDiff, ↓reduceDIte, harr0, harr1,
          eqToHom_refl, Category.id_comp, Category.comp_id]
        exact hφ⟩
    · exact ⟨0, by simp [twoTermDiff, h]⟩

/-- The filtration on the two-term complex is bounded when the convergence
    filtrations `F₁` and `F₂` are bounded. -/
noncomputable def underlyingComplexBounded
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    (aMap : ∀ k', A₁ k' ⟶ A₂ k')
    (hcompat : ∀ (s : ℤ) (k' : ω'),
      ∃ (φ : Subobject.underlying.obj (F₁.F s k') ⟶
             Subobject.underlying.obj (F₂.F s k')),
        φ ≫ (F₂.F s k').arrow = (F₁.F s k').arrow ≫ aMap k')
    (t : ω')
    (bnd₁ : F₁.IsBounded) (bnd₂ : F₂.IsBounded) :
    (underlyingComplex aMap hcompat t).IsBounded where
  lo := fun k =>
    if k = 1 then bnd₁.lo t else if k = 0 then bnd₂.lo t else 0
  hi := fun k =>
    if k = 1 then bnd₁.hi t else if k = 0 then bnd₂.hi t else 0
  lo_le_hi := fun k => by
    by_cases h₁ : k = 1
    · simp only [h₁, ↓reduceIte]; exact bnd₁.lo_le_hi t
    · by_cases h₀ : k = 0
      · simp only [h₀, ↓reduceIte]; exact bnd₂.lo_le_hi t
      · simp [h₁, h₀]
  boundedBelow := fun k s hs => by
    simp only [underlyingComplex, twoTermFil]
    by_cases h₁ : k = 1
    · subst h₁; simp only [↓reduceDIte] at hs ⊢; exact bnd₁.boundedBelow t s hs
    · by_cases h₀ : k = 0
      · subst h₀; simp only [h₁, ↓reduceDIte] at hs ⊢; exact bnd₂.boundedBelow t s hs
      · simp [h₁, h₀]
  boundedAbove := fun k s hs => by
    simp only [underlyingComplex, twoTermFil]
    by_cases h₁ : k = 1
    · subst h₁; simp only [↓reduceDIte] at hs ⊢; exact bnd₁.boundedAbove t s hs
    · by_cases h₀ : k = 0
      · subst h₀; simp only [h₁, ↓reduceDIte] at hs ⊢; exact bnd₂.boundedAbove t s hs
      · simp only [h₁, h₀] at hs
        have hz : IsZero (twoTermObj (A₁ t) (A₂ t) k) := by
          have : twoTermObj (A₁ t) (A₂ t) k = ⊥_ C := by
            simp [twoTermObj, if_neg h₁, if_neg h₀]
          rw [this]
          apply IsInitial.isZero; exact initialIsInitial
        simp only [dif_neg h₁, dif_neg h₀]
        exact subobject_eq_bot_of_isZero hz ⊤

/-! ### Extension spectral sequence

The extension spectral sequence (ESS) associated to a morphism of converging
spectral sequences. For each stem degree `t`, the ESS is the spectral sequence
of the two-term filtered complex `A₁(t) → A₂(t)`.

使用此构造时必须区分三个谱序列：

* `E₁ : SpectralSequence C ω` 是收敛到过滤对象 `(A₁, F₁)` 的输入谱序列。
* `E₂ : SpectralSequence C ω` 是收敛到 `(A₂, F₂)` 的输入谱序列。
  收敛态射包含 `eMap : E₁∞ ⟶ E₂∞` 与 `aMap : A₁ ⟶ A₂`，
  相容方块连接这两个映射。
* `ext.ess t : SpectralSequence C (ℤ × ℤ)` 是第三个谱序列，
  由过滤两项复形 `A₁(t) →[aMap t] A₂(t)` 构造。其 `E₀` 项是
  `A₁(t)`、`A₂(t)` 的关联分次，经收敛同构与 `E₁∞`、`E₂∞` 对应。
  这并不意味着三个谱序列相等。

因此 `E₁` 和 `E₂` 不是 `ext.ess t` 的源页、目标页名称；
输入谱序列自身的页微分与 `ext.ess t` 的扩张微分属于不同谱序列。 -/

variable {ω : Type w} [AddCommGroup ω] [DecidableEq ω]

/-- The extension spectral sequence data, parameterized by a convergence
    morphism and bounded filtration hypotheses. For each stem degree `t`,
    this produces a spectral sequence indexed by `ℤ × ℤ` via
    `FilteredComplex.toSpectralSequence`. -/
structure BoundedExtensionSS
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    (conv₁ : Convergence E₁ A₁ F₁) (conv₂ : Convergence E₂ A₂ F₂)
    (cm : ConvergenceMorphism conv₁ conv₂)
    (bnd₁ : F₁.IsBounded) (bnd₂ : F₂.IsBounded) : Prop where

/-- The underlying two-term filtered complex at each stem degree. -/
noncomputable def BoundedExtensionSS.complex
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    {bnd₁ : F₁.IsBounded} {bnd₂ : F₂.IsBounded}
    (_ext : BoundedExtensionSS conv₁ conv₂ cm bnd₁ bnd₂) (t : ω') : FilteredComplex C :=
  underlyingComplex cm.aMap cm.filtration_compat t

/-- Boundedness of the underlying complex at each stem. -/
noncomputable def BoundedExtensionSS.bounded
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    {bnd₁ : F₁.IsBounded} {bnd₂ : F₂.IsBounded}
    (ext : BoundedExtensionSS conv₁ conv₂ cm bnd₁ bnd₂) (t : ω') :
    (ext.complex t).IsBounded :=
  underlyingComplexBounded cm.aMap cm.filtration_compat t bnd₁ bnd₂

/-- The extension spectral sequence at stem degree `t`:
    the spectral sequence associated to the two-term filtered complex
    `A₁(t) → A₂(t)`. -/
noncomputable def BoundedExtensionSS.ess
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    {bnd₁ : F₁.IsBounded} {bnd₂ : F₂.IsBounded}
    (ext : BoundedExtensionSS conv₁ conv₂ cm bnd₁ bnd₂) (t : ω') :
    SpectralSequence C (ℤ × ℤ) :=
  (ext.complex t).toSpectralSequence (ext.bounded t)

/-- The default `BoundedExtensionSS` instance using the standard construction. -/
noncomputable def BoundedExtensionSS.mk'
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    (conv₁ : Convergence E₁ A₁ F₁) (conv₂ : Convergence E₂ A₂ F₂)
    (cm : ConvergenceMorphism conv₁ conv₂)
    (bnd₁ : F₁.IsBounded) (bnd₂ : F₂.IsBounded) :
    BoundedExtensionSS conv₁ conv₂ cm bnd₁ bnd₂ := ⟨⟩

/-- The weak convergence of the extension spectral sequence at stem `t`:
    the ESS converges to the homology of the two-term complex `A₁(t) → A₂(t)`. -/
noncomputable def BoundedExtensionSS.weakConvergence
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    {bnd₁ : F₁.IsBounded} {bnd₂ : F₂.IsBounded}
    (ext : BoundedExtensionSS conv₁ conv₂ cm bnd₁ bnd₂) (t : ω') :
    Convergence (ext.ess t)
      (ext.complex t).homologyObj (ext.complex t).homologyFiltration :=
  (ext.complex t).weakConvergence (ext.bounded t)

/-! ### E₀-page structure

The E₀-page of the ESS at bidegree `(s, k)` is the associated graded
`gr^s` of the two-term complex. For `k = 1`, this is `gr^s(A₁) ≅ E∞(V₁)`,
and for `k = 0`, this is `gr^s(A₂) ≅ E∞(V₂)`.

The E₀-page differential only has the `(s, 1) → (s, 0)` component nonzero,
which defines the ESS differential `d₀^f`. -/

/-- The E₀-page of the ESS at `(s, 1)` is the associated graded of
    `A₁(t)` at filtration degree `s`, i.e., `F₁^s / F₁^{s+1}`.
    This equals `E∞^s(V₁)` under the convergence isomorphism. -/
noncomputable def BoundedExtensionSS.e0PageAtOne
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    {bnd₁ : F₁.IsBounded} {bnd₂ : F₂.IsBounded}
    (ext : BoundedExtensionSS conv₁ conv₂ cm bnd₁ bnd₂) (t : ω') (s : ℤ) : C :=
  (ext.complex t).assocGraded s 1

/-- The E₀-page of the ESS at `(s, 0)` is the associated graded of
    `A₂(t)` at filtration degree `s`, i.e., `F₂^s / F₂^{s+1}`.
    This equals `E∞^s(V₂)` under the convergence isomorphism. -/
noncomputable def BoundedExtensionSS.e0PageAtZero
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    {bnd₁ : F₁.IsBounded} {bnd₂ : F₂.IsBounded}
    (ext : BoundedExtensionSS conv₁ conv₂ cm bnd₁ bnd₂) (t : ω') (s : ℤ) : C :=
  (ext.complex t).assocGraded s 0

/-- The E₀-page at `(s, 1)` of the ESS equals the associated graded of
    the `F₁`-filtration on `A₁(t)` at filtration degree `s`. -/
theorem BoundedExtensionSS.e0PageAtOne_eq
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    {bnd₁ : F₁.IsBounded} {bnd₂ : F₂.IsBounded}
    (ext : BoundedExtensionSS conv₁ conv₂ cm bnd₁ bnd₂) (t : ω') (s : ℤ) :
    ext.e0PageAtOne t s = F₁.associatedGraded s t := by
  simp only [e0PageAtOne, BoundedExtensionSS.complex, underlyingComplex, FilteredComplex.assocGraded,
    Filtration.associatedGraded]
  congr 1

/-- The E₀-page at `(s, 0)` of the ESS equals the associated graded of
    the `F₂`-filtration on `A₂(t)` at filtration degree `s`. -/
theorem BoundedExtensionSS.e0PageAtZero_eq
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    {bnd₁ : F₁.IsBounded} {bnd₂ : F₂.IsBounded}
    (ext : BoundedExtensionSS conv₁ conv₂ cm bnd₁ bnd₂) (t : ω') (s : ℤ) :
    ext.e0PageAtZero t s = F₂.associatedGraded s t := by
  simp only [e0PageAtZero, BoundedExtensionSS.complex, underlyingComplex, FilteredComplex.assocGraded,
    Filtration.associatedGraded]
  congr 1

/-- The d₀ differential of the ESS at `(s, 1) → (s, 0)` is the map on
    associated graded pieces induced by `cm.aMap`:
    `gr^s(A₁, t) → gr^s(A₂, t)`. -/
noncomputable def BoundedExtensionSS.d0
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    {bnd₁ : F₁.IsBounded} {bnd₂ : F₂.IsBounded}
    (ext : BoundedExtensionSS conv₁ conv₂ cm bnd₁ bnd₂) (t : ω') (s : ℤ) :
    ext.e0PageAtOne t s ⟶ ext.e0PageAtZero t s :=
  (ext.complex t).assocGradedDiff s 1

/-- `d₀` equals the induced map on associated graded pieces from `cm.aMap`. -/
theorem BoundedExtensionSS.d0_eq_inducedAssocGradedMap
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    {bnd₁ : F₁.IsBounded} {bnd₂ : F₂.IsBounded}
    (ext : BoundedExtensionSS conv₁ conv₂ cm bnd₁ bnd₂) (t : ω') (s : ℤ) :
    ext.d0 t s =
      eqToHom (ext.e0PageAtOne_eq t s) ≫
        Filtration.inducedAssocGradedMap cm.aMap cm.filtration_compat s t ≫
        eqToHom (ext.e0PageAtZero_eq t s).symm := by
  simp only [d0, BoundedExtensionSS.complex]
  set FC := underlyingComplex cm.aMap cm.filtration_compat t with hFC
  change FC.assocGradedDiff s 1 = _
  -- The two-term filtration at k=1,0 agrees with F₁,F₂ (def'ly for Subobjects, prop'ly for ofLE).
  have hofLE1 : Subobject.ofLE (FC.fil (s + 1) 1) (FC.fil s 1) (FC.fil_anti s 1) =
      Subobject.ofLE (F₁.F (s + 1) t) (F₁.F s t) (F₁.mono s t) := by
    simp [FC, underlyingComplex, twoTermFil]
  have hofLE0 : Subobject.ofLE (FC.fil (s + 1) (1 - 1)) (FC.fil s (1 - 1))
      (FC.fil_anti s (1 - 1)) =
      Subobject.ofLE (F₂.F (s + 1) t) (F₂.F s t) (F₂.mono s t) := by
    simp [FC, underlyingComplex, twoTermFil]
  -- Unfold assocGradedDiff to cokernel.desc, then cancel the epi cokernel.π.
  simp only [FilteredComplex.assocGradedDiff, FilteredComplex.assocGraded, id_eq]
  apply (cancel_epi (cokernel.π (Subobject.ofLE (FC.fil (s + 1) 1) (FC.fil s 1)
    (FC.fil_anti s 1)))).mp
  rw [cokernel.π_desc]
  -- Simplify the eqToHom transports (they are identities since twoTermFil reduces def'ly).
  simp only [Filtration.inducedAssocGradedMap,
    eqToHom_refl, Category.id_comp, Category.comp_id]
  -- Unfold cokernel.map to cokernel.desc and use `change` to syntactically unify
  -- the ofLE arguments (definitionally equal but syntactically different).
  unfold cokernel.map
  change (FC.d_preserves_fil s 1).choose ≫
    cokernel.π (Subobject.ofLE (F₂.F (s + 1) t) (F₂.F s t) (F₂.mono s t)) =
    cokernel.π (Subobject.ofLE (F₁.F (s + 1) t) (F₁.F s t) (F₁.mono s t)) ≫
    cokernel.desc (Subobject.ofLE (F₁.F (s + 1) t) (F₁.F s t) (F₁.mono s t))
      ((cm.filtration_compat s t).choose ≫
        cokernel.π (Subobject.ofLE (F₂.F (s + 1) t) (F₂.F s t) (F₂.mono s t))) _
  rw [cokernel.π_desc]
  -- Both sides are now `_.choose ≫ cokernel.π _`; show the two .choose's agree.
  congr 1
  apply (cancel_mono (F₂.F s t).arrow).mp
  rw [(cm.filtration_compat s t).choose_spec]
  -- Remains: (FC.d_preserves_fil s 1).choose ≫ (F₂.F s t).arrow = (F₁.F s t).arrow ≫ cm.aMap t
  -- This follows from (FC.d_preserves_fil s 1).choose_spec after unfolding twoTermFil/twoTermDiff.
  convert (FC.d_preserves_fil s 1).choose_spec using 1 <;> try rfl
  change (F₁.F s t).arrow ≫ cm.aMap t =
    (twoTermFil (fun s => F₁.F s t) (fun s => F₂.F s t) s 1).arrow ≫
      twoTermDiff (A₁ t) (A₂ t) (cm.aMap t) 1
  simp [twoTermFil, twoTermDiff, twoTermObj]

/-! ### Three-spectra chain

Given a composable pair of convergence morphisms
`V₁ →[f] V₂ →[g] V₃`, the three-spectra chain packages both the
`f`-ESS and `g`-ESS together with their relationship. -/

/-- A composable pair of convergence morphisms `V₁ → V₂ → V₃`. -/
structure ThreeSpectraChain
    {E₁ E₂ E₃ : SpectralSequence C ω}
    {A₁ A₂ A₃ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂} {F₃ : Filtration A₃}
    (conv₁ : Convergence E₁ A₁ F₁)
    (conv₂ : Convergence E₂ A₂ F₂)
    (conv₃ : Convergence E₃ A₃ F₃) where
  /-- The first convergence morphism `V₁ → V₂`. -/
  cm₁₂ : ConvergenceMorphism conv₁ conv₂
  /-- The second convergence morphism `V₂ → V₃`. -/
  cm₂₃ : ConvergenceMorphism conv₂ conv₃
  /-- Bounded filtration on the first abutment. -/
  bnd₁ : F₁.IsBounded
  /-- Bounded filtration on the second abutment. -/
  bnd₂ : F₂.IsBounded
  /-- Bounded filtration on the third abutment. -/
  bnd₃ : F₃.IsBounded

/-- The f-extension spectral sequence from the three-spectra chain. -/
noncomputable def ThreeSpectraChain.boundedEssF
    {E₁ E₂ E₃ : SpectralSequence C ω}
    {A₁ A₂ A₃ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂} {F₃ : Filtration A₃}
    {conv₁ : Convergence E₁ A₁ F₁}
    {conv₂ : Convergence E₂ A₂ F₂}
    {conv₃ : Convergence E₃ A₃ F₃}
    (chain : ThreeSpectraChain conv₁ conv₂ conv₃) :
    BoundedExtensionSS conv₁ conv₂ chain.cm₁₂ chain.bnd₁ chain.bnd₂ :=
  BoundedExtensionSS.mk' conv₁ conv₂ chain.cm₁₂ chain.bnd₁ chain.bnd₂

/-- The g-extension spectral sequence from the three-spectra chain. -/
noncomputable def ThreeSpectraChain.boundedEssG
    {E₁ E₂ E₃ : SpectralSequence C ω}
    {A₁ A₂ A₃ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂} {F₃ : Filtration A₃}
    {conv₁ : Convergence E₁ A₁ F₁}
    {conv₂ : Convergence E₂ A₂ F₂}
    {conv₃ : Convergence E₃ A₃ F₃}
    (chain : ThreeSpectraChain conv₁ conv₂ conv₃) :
    BoundedExtensionSS conv₂ conv₃ chain.cm₂₃ chain.bnd₂ chain.bnd₃ :=
  BoundedExtensionSS.mk' conv₂ conv₃ chain.cm₂₃ chain.bnd₂ chain.bnd₃

/-! ### Abstract ESS accessors and detection set

The ESS itself is indexed by `(filtration, complex degree) : ℤ × ℤ` at a
fixed abutment degree `t : ω'`.  The following accessors therefore use that
concrete index rather than pretending that an arbitrary input grading `ω`
canonically identifies with the ESS grading. -/

/-- The subtype of abutment elements detected by an E∞ class `y` at bidegree
    `k`. An element `x : T ⟶ F^s A^{k'}` belongs to the detection set of `y`
    if `Detects conv y x` holds, where `(s, k') = conv.reindex k`. -/
def DetectionSet
    {E : SpectralSequence C ω} {A : ω' → C} {F : Filtration A}
    (conv : Convergence E A F) {T : C} (k : ω)
    (y : T ⟶ (E.ssData k).eInfty) :=
  { x : T ⟶ Subobject.underlying.obj (F.F (conv.reindex k).1 (conv.reindex k).2) //
    Detects conv y x }

/-- The page-`r` differential of the extension spectral sequence at fixed
abutment degree `t` and ESS bidegree `k = (filtration, complex degree)`. -/
noncomputable def BoundedExtensionSS.essDiff
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    {bnd₁ : F₁.IsBounded} {bnd₂ : F₂.IsBounded}
    (ext : BoundedExtensionSS conv₁ conv₂ cm bnd₁ bnd₂)
    (t : ω') (r : ℤ) (k : ℤ × ℤ) :
    (ext.ess t).Page r k ⟶
      (ext.ess t).Page r (k + (ext.ess t).diffDeg r) :=
  (ext.ess t).d r k

/-- The image object of an ESS differential.  This is the categorical version
of the subgroup of page-`r` boundaries contributed by that differential. -/
noncomputable def BoundedExtensionSS.essBoundary
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    {bnd₁ : F₁.IsBounded} {bnd₂ : F₂.IsBounded}
    (ext : BoundedExtensionSS conv₁ conv₂ cm bnd₁ bnd₂)
    (t : ω') (r : ℤ) (k : ℤ × ℤ) : C :=
  Subobject.underlying.obj (imageSubobject (ext.essDiff t r k))

/-- An essential `f`-extension at `(t,r,k)` means that the corresponding ESS
differential is nonzero. -/
abbrev HasFExtension
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    {bnd₁ : F₁.IsBounded} {bnd₂ : F₂.IsBounded}
    (ext : BoundedExtensionSS conv₁ conv₂ cm bnd₁ bnd₂)
    (t : ω') (r : ℤ) (k : ℤ × ℤ) : Prop :=
  ext.essDiff t r k ≠ 0

/-- **ESS 的 non-crossing 唯一性引理**：
    设 ESS（由过滤复形 `ext.complex` 给出的谱序列）中有一条
    微分关系 `d_r` 从 `(s, k)` 到 `(s+r, k-1)`，
    且该关系**不被任何本质关系 cross**。
    则对任意被它 detect 的类（`T` 投射，`x y` 为其源/目标的
    广义元素）以及任意 lift `xl`：若 `xl` 的复形微分落入更深过滤
    （经 `yl` 与 `F^{s+r} ↪ F^s` 的包含分解），则该微分必是
    原目标 `y` 的 lift——即「所关联的微分就是一开始的微分」。
    证明：直接调用 `FilteredComplex.lift_rel_of_not_crossed`。 -/
theorem BoundedExtensionSS.rel_eq_of_not_crossed
    {E₁ E₂ : SpectralSequence C ω}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    {bnd₁ : F₁.IsBounded} {bnd₂ : F₂.IsBounded}
    (ext : BoundedExtensionSS conv₁ conv₂ cm bnd₁ bnd₂)
    (t : ω') (r : ℤ) (hr : 0 ≤ r) (s k : ℤ) {T : C} [Projective T]
    {x : T ⟶ (ext.complex t).assocGraded s k}
    {y₁ : T ⟶ (ext.complex t).assocGraded (s + r) (k - 1)}
    (h₁ : DifferentialRelation ((ext.complex t).toSpectralSequence (ext.bounded t))
      r ⟨s, k⟩ x y₁)
    (hnc : ¬ RelationCrossedBy ((ext.complex t).toSpectralSequence (ext.bounded t))
      (fun p => p.1) r ⟨s, k⟩ x y₁ h₁)
    {xl : T ⟶ Subobject.underlying.obj ((ext.complex t).fil s k)}
    (hx : (ext.complex t).IsLift s k xl x)
    (yl : T ⟶ Subobject.underlying.obj ((ext.complex t).fil (s + r) (k - 1)))
    (hd : xl ≫ (ext.complex t).filDiff s k =
      yl ≫ Subobject.ofLE ((ext.complex t).fil (s + r) (k - 1))
        ((ext.complex t).fil s (k - 1))
        ((ext.complex t).fil_anti_of_le (k - 1) (by omega))) :
    (ext.complex t).IsLift (s + r) (k - 1) yl y₁ :=
  FilteredComplex.lift_rel_of_not_crossed (ext.complex t) (ext.bounded t)
    r hr s k h₁ hnc hx yl hd

/-! ### 过滤复形的范畴 -/

/-- 过滤复形的**态射**：分次映射族 `f k : FC₁.A k ⟶ FC₂.A k`，
    与微分交换（链映射条件 `d ≫ f = f ≫ d`），且保过滤
    （对每个 `(s, k)` 存在过滤层之间的提升 `φ`，使 `φ ≫ arrow = arrow ≫ f k`）。
    保过滤提升是 ∃-命题数据，供诱导关联分次映射使用。 -/
structure FilteredComplexMorphism (FC₁ FC₂ : FilteredComplex C) where
  /-- 每个次数 `k` 上底层对象之间的映射 -/
  f : ∀ k, FC₁.A k ⟶ FC₂.A k
  /-- 与微分交换：`f k ≫ d k = d k ≫ f (k-1)` -/
  comm_d : ∀ k, f k ≫ FC₂.d k = FC₁.d k ≫ f (k - 1)
  /-- 保过滤：对每个 `(s, k)`，`f k` 在过滤层 `F^s` 之间的限制存在 -/
  filt_compat : ∀ s k,
    ∃ (φ : Subobject.underlying.obj (FC₁.fil s k) ⟶
           Subobject.underlying.obj (FC₂.fil s k)),
      φ ≫ (FC₂.fil s k).arrow = (FC₁.fil s k).arrow ≫ f k

/-- 两项过滤复形的标准态射构造。给定两个链复形分量上的映射、
    链映射方块和两个过滤相容性，在次数 `1` 和 `0` 取这两个映射，
    其余次数取零态射。 -/
noncomputable def underlyingComplexMorphism
    {τ : Type w}
    {A₁ A₂ B₁ B₂ : τ → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {G₁ : Filtration B₁} {G₂ : Filtration B₂}
    (aMap : ∀ t, A₁ t ⟶ A₂ t)
    (aCompat : ∀ (s : ℤ) (t : τ),
      ∃ φ, φ ≫ (F₂.F s t).arrow = (F₁.F s t).arrow ≫ aMap t)
    (bMap : ∀ t, B₁ t ⟶ B₂ t)
    (bCompat : ∀ (s : ℤ) (t : τ),
      ∃ φ, φ ≫ (G₂.F s t).arrow = (G₁.F s t).arrow ≫ bMap t)
    (u₁ : ∀ t, A₁ t ⟶ B₁ t) (u₂ : ∀ t, A₂ t ⟶ B₂ t)
    (comm : ∀ t, u₁ t ≫ bMap t = aMap t ≫ u₂ t)
    (compat₁ : ∀ (s : ℤ) (t : τ),
      ∃ φ, φ ≫ (G₁.F s t).arrow = (F₁.F s t).arrow ≫ u₁ t)
    (compat₂ : ∀ (s : ℤ) (t : τ),
      ∃ φ, φ ≫ (G₂.F s t).arrow = (F₂.F s t).arrow ≫ u₂ t)
    (t : τ) :
    FilteredComplexMorphism
      (underlyingComplex aMap aCompat t) (underlyingComplex bMap bCompat t) := by
  let component : ∀ k : ℤ,
      (underlyingComplex aMap aCompat t).A k ⟶
        (underlyingComplex bMap bCompat t).A k := fun k =>
    if h₁ : k = 1 then
      eqToHom (by simp [underlyingComplex, twoTermObj, h₁]) ≫ u₁ t ≫
        eqToHom (by simp [underlyingComplex, twoTermObj, h₁])
    else if h₀ : k = 0 then
      eqToHom (by simp [underlyingComplex, twoTermObj, h₀]) ≫ u₂ t ≫
        eqToHom (by simp [underlyingComplex, twoTermObj, h₀])
    else 0
  refine { f := component, comm_d := ?_, filt_compat := ?_ }
  · intro k
    by_cases h₁ : k = 1
    · subst k
      simpa [component, underlyingComplex, twoTermDiff, twoTermObj] using comm t
    · simp [component, underlyingComplex, twoTermDiff, twoTermObj, h₁]
  · intro s k
    by_cases h₁ : k = 1
    · subst k
      simpa [component, underlyingComplex, twoTermFil, twoTermObj] using compat₁ s t
    · by_cases h₀ : k = 0
      · subst k
        simpa [component, underlyingComplex, twoTermFil, twoTermObj] using compat₂ s t
      · refine ⟨0, ?_⟩
        simp [component, underlyingComplex, twoTermFil, twoTermObj, h₁, h₀]

/-- 过滤复形态射在关联分次 `gr^s A^k` 上诱导的映射：
    由保过滤提升经 `cokernel.map` 构造（同 `Filtration.inducedAssocGradedMap` 的模式）。 -/
noncomputable def FilteredComplexMorphism.assocGradedMap
    {FC₁ FC₂ : FilteredComplex C} (g : FilteredComplexMorphism FC₁ FC₂)
    (s k : ℤ) : FC₁.assocGraded s k ⟶ FC₂.assocGraded s k :=
  cokernel.map
    (Subobject.ofLE (FC₁.fil (s + 1) k) (FC₁.fil s k) (FC₁.fil_anti s k))
    (Subobject.ofLE (FC₂.fil (s + 1) k) (FC₂.fil s k) (FC₂.fil_anti s k))
    (g.filt_compat (s + 1) k).choose
    (g.filt_compat s k).choose
    (by
      apply (cancel_mono ((FC₂.fil s k).arrow)).mp
      simp only [Category.assoc, Subobject.ofLE_arrow]
      rw [(g.filt_compat s k).choose_spec, (g.filt_compat (s + 1) k).choose_spec,
        ← Category.assoc, Subobject.ofLE_arrow])

/-- 广义关联分次映射（显式提升族版本）：把 `filt_compat` 的提升族
    换成显式参数 `φ`，避免 `.choose` 在 rw 时产生 motive 障碍。
    与 `assocGradedMap` 在 `φ := (g.filt_compat _ _).choose` 处定义相等。 -/
noncomputable def FilteredComplexMorphism.assocGradedMapOfMap
    {FC₁ FC₂ : FilteredComplex C}
    (φ : ∀ (s k : ℤ), Subobject.underlying.obj (FC₁.fil s k) ⟶
      Subobject.underlying.obj (FC₂.fil s k))
    (hw : ∀ (s k : ℤ),
      Subobject.ofLE (FC₁.fil (s + 1) k) (FC₁.fil s k) (FC₁.fil_anti s k) ≫ φ s k =
        φ (s + 1) k ≫ Subobject.ofLE (FC₂.fil (s + 1) k) (FC₂.fil s k) (FC₂.fil_anti s k))
    (s k : ℤ) : FC₁.assocGraded s k ⟶ FC₂.assocGraded s k :=
  cokernel.map
    (Subobject.ofLE (FC₁.fil (s + 1) k) (FC₁.fil s k) (FC₁.fil_anti s k))
    (Subobject.ofLE (FC₂.fil (s + 1) k) (FC₂.fil s k) (FC₂.fil_anti s k))
    (φ (s + 1) k) (φ s k) (hw s k)

/-- 广义关联分次映射的同余性：提升族相等则诱导映射相等。 -/
theorem FilteredComplexMorphism.assocGradedMapOfMap_congr
    {FC₁ FC₂ : FilteredComplex C}
    {φ ψ : ∀ (s k : ℤ), Subobject.underlying.obj (FC₁.fil s k) ⟶
      Subobject.underlying.obj (FC₂.fil s k)}
    (hwφ : ∀ (s k : ℤ),
      Subobject.ofLE (FC₁.fil (s + 1) k) (FC₁.fil s k) (FC₁.fil_anti s k) ≫ φ s k =
        φ (s + 1) k ≫ Subobject.ofLE (FC₂.fil (s + 1) k) (FC₂.fil s k) (FC₂.fil_anti s k))
    (hwψ : ∀ (s k : ℤ),
      Subobject.ofLE (FC₁.fil (s + 1) k) (FC₁.fil s k) (FC₁.fil_anti s k) ≫ ψ s k =
        ψ (s + 1) k ≫ Subobject.ofLE (FC₂.fil (s + 1) k) (FC₂.fil s k) (FC₂.fil_anti s k))
    (h : φ = ψ) (s k : ℤ) :
    FilteredComplexMorphism.assocGradedMapOfMap φ hwφ s k =
      FilteredComplexMorphism.assocGradedMapOfMap ψ hwψ s k := by
  subst h
  rfl

/-- 广义关联分次映射的恒等性：恒等提升诱导恒等映射。
    用 `cokernel.π` 的外满性消去后直接化简。 -/
theorem FilteredComplexMorphism.assocGradedMapOfMap_id
    (FC : FilteredComplex C) (s k : ℤ) :
    FilteredComplexMorphism.assocGradedMapOfMap
      (fun _ _ => 𝟙 _) (fun s k => by simp) s k = 𝟙 (FC.assocGraded s k) := by
  apply (cancel_epi (cokernel.π _)).mp
  simp only [FilteredComplexMorphism.assocGradedMapOfMap, cokernel.map, cokernel.π_desc,
    Category.id_comp]
  show cokernel.π _ = cokernel.π _ ≫ 𝟙 (cokernel _)
  simp only [Category.comp_id]

/-- 广义关联分次映射的复合性：复合提升诱导复合映射。 -/
theorem FilteredComplexMorphism.assocGradedMapOfMap_comp
    {FC₁ FC₂ FC₃ : FilteredComplex C}
    (φ : ∀ (s k : ℤ), Subobject.underlying.obj (FC₁.fil s k) ⟶
      Subobject.underlying.obj (FC₂.fil s k))
    (ψ : ∀ (s k : ℤ), Subobject.underlying.obj (FC₂.fil s k) ⟶
      Subobject.underlying.obj (FC₃.fil s k))
    (hwφ : ∀ (s k : ℤ),
      Subobject.ofLE (FC₁.fil (s + 1) k) (FC₁.fil s k) (FC₁.fil_anti s k) ≫ φ s k =
        φ (s + 1) k ≫ Subobject.ofLE (FC₂.fil (s + 1) k) (FC₂.fil s k) (FC₂.fil_anti s k))
    (hwψ : ∀ (s k : ℤ),
      Subobject.ofLE (FC₂.fil (s + 1) k) (FC₂.fil s k) (FC₂.fil_anti s k) ≫ ψ s k =
        ψ (s + 1) k ≫ Subobject.ofLE (FC₃.fil (s + 1) k) (FC₃.fil s k) (FC₃.fil_anti s k))
    (hwφψ : ∀ (s k : ℤ),
      Subobject.ofLE (FC₁.fil (s + 1) k) (FC₁.fil s k) (FC₁.fil_anti s k) ≫ (φ s k ≫ ψ s k) =
        (φ (s + 1) k ≫ ψ (s + 1) k) ≫
          Subobject.ofLE (FC₃.fil (s + 1) k) (FC₃.fil s k) (FC₃.fil_anti s k))
    (s k : ℤ) :
    FilteredComplexMorphism.assocGradedMapOfMap
        (fun s k => φ s k ≫ ψ s k) hwφψ s k =
      FilteredComplexMorphism.assocGradedMapOfMap φ hwφ s k ≫
        FilteredComplexMorphism.assocGradedMapOfMap ψ hwψ s k := by
  apply (cancel_epi (cokernel.π _)).mp
  simp only [FilteredComplexMorphism.assocGradedMapOfMap, cokernel.map, cokernel.π_desc_assoc,
    cokernel.π_desc, Category.assoc]

/-- 恒等过滤复形态射：逐次数取恒等映射。
    显式命名以避免 `𝟙` 在 `Category (FilteredComplex C)` 实例
    声明之前不可用的问题。 -/
def FilteredComplexMorphism.id (FC : FilteredComplex C) :
    FilteredComplexMorphism FC FC where
  f := fun _ => 𝟙 _
  comm_d := fun _ => by simp
  filt_compat := fun s k => ⟨𝟙 _, by simp⟩

/-- 复合过滤复形态射：逐次数取复合，微分交换与保过滤提升
    取两次的复合（与 `Category (FilteredComplex C)` 实例中的 `comp`
    定义一致；显式命名以避免实例声明顺序问题）。 -/
def FilteredComplexMorphism.comp {FC₁ FC₂ FC₃ : FilteredComplex C}
    (g : FilteredComplexMorphism FC₁ FC₂) (h : FilteredComplexMorphism FC₂ FC₃) :
    FilteredComplexMorphism FC₁ FC₃ where
  f := fun k => g.f k ≫ h.f k
  comm_d := fun k => by
    rw [Category.assoc, h.comm_d, ← Category.assoc, g.comm_d, Category.assoc]
  filt_compat := fun s k =>
    ⟨(g.filt_compat s k).choose ≫ (h.filt_compat s k).choose, by
      rw [Category.assoc, (h.filt_compat s k).choose_spec,
        ← Category.assoc, (g.filt_compat s k).choose_spec, Category.assoc]⟩

/-- 桥接引理：`assocGradedMap` 等于显式参数版本在 choose 提升处的取值
    （两边同为 `cokernel.map` 同一组参数），由 `rfl` 即得；
    价值在于把 `.choose` 从 rw 目标中剥离到等式右端。 -/
theorem FilteredComplexMorphism.assocGradedMap_eq
    {FC₁ FC₂ : FilteredComplex C} (g : FilteredComplexMorphism FC₁ FC₂) (s k : ℤ) :
    g.assocGradedMap s k =
      FilteredComplexMorphism.assocGradedMapOfMap
        (fun s k => (g.filt_compat s k).choose)
        (fun s k => by
          apply (cancel_mono ((FC₂.fil s k).arrow)).mp
          simp only [Category.assoc, Subobject.ofLE_arrow]
          rw [(g.filt_compat s k).choose_spec, (g.filt_compat (s + 1) k).choose_spec,
            ← Category.assoc, Subobject.ofLE_arrow]) s k :=
  rfl

/-- 过滤复形态射在关联分次上映射的恒等性：
    恒等态射的 `assocGradedMap` 等于恒等映射。
    先经桥接引理转成广义版本，再把 `filt_compat` 的 choose 提升
    （恒等态射下其见证即 `𝟙`，由 `cancel_mono arrow` 论证）替换为恒等提升，
    最后调用广义恒等引理。 -/
theorem FilteredComplexMorphism.assocGradedMap_id
    (FC : FilteredComplex C) (s k : ℤ) :
    FilteredComplexMorphism.assocGradedMap
      (FilteredComplexMorphism.id FC : FilteredComplexMorphism FC FC) s k =
      𝟙 (FC.assocGraded s k) := by
  rw [FilteredComplexMorphism.assocGradedMap_eq
    (FilteredComplexMorphism.id FC : FilteredComplexMorphism FC FC)]
  have h : (fun s k : ℤ =>
        ((FilteredComplexMorphism.id FC :
          FilteredComplexMorphism FC FC).filt_compat s k).choose) =
      fun _ _ => 𝟙 _ := by
    funext s k
    apply (cancel_mono ((FC.fil s k).arrow)).mp
    rw [((FilteredComplexMorphism.id FC :
      FilteredComplexMorphism FC FC).filt_compat s k).choose_spec]
    simp only [FilteredComplexMorphism.id, Category.comp_id, Category.id_comp]
  rw [FilteredComplexMorphism.assocGradedMapOfMap_congr
    (fun s k => by
      apply (cancel_mono ((FC.fil s k).arrow)).mp
      simp only [Category.assoc, Subobject.ofLE_arrow]
      rw [((FilteredComplexMorphism.id FC :
        FilteredComplexMorphism FC FC).filt_compat s k).choose_spec,
        ((FilteredComplexMorphism.id FC :
          FilteredComplexMorphism FC FC).filt_compat (s + 1) k).choose_spec,
        ← Category.assoc, Subobject.ofLE_arrow])
    (fun s k => by simp) h s k]
  exact FilteredComplexMorphism.assocGradedMapOfMap_id FC s k

/-- 过滤复形态射的外延性：两态射的 `f` 分量相同则相等
    （其余字段都是 Prop，proof irrelevance）。 -/
theorem FilteredComplexMorphism.ext {FC₁ FC₂ : FilteredComplex C}
    {g h : FilteredComplexMorphism FC₁ FC₂} (e : g.f = h.f) : g = h := by
  rcases g with ⟨gf, _, _⟩; rcases h with ⟨hf, _, _⟩
  subst e; rfl

/-- 过滤复形的范畴结构：态射为 `FilteredComplexMorphism`。
    恒等取恒等映射族；复合逐分量复合（保过滤提升取两次提升的复合）。
    范畴公理由 `FilteredComplexMorphism.ext` 归约到 `f` 分量。 -/
noncomputable instance : Category (FilteredComplex C) where
  Hom FC₁ FC₂ := FilteredComplexMorphism FC₁ FC₂
  id FC := FilteredComplexMorphism.id FC
  comp g h := FilteredComplexMorphism.comp g h
  id_comp g := FilteredComplexMorphism.ext (funext fun k => Category.id_comp (g.f k))
  comp_id g := FilteredComplexMorphism.ext (funext fun k => Category.comp_id (g.f k))
  assoc g h l :=
    FilteredComplexMorphism.ext (funext fun k => Category.assoc (g.f k) (h.f k) (l.f k))

/-- **有界**过滤复形：过滤复形打包其有界性证明（IsBounded 是 Prop 打包进对象）。 -/
structure BoundedFilteredComplex (C : Type u) [Category.{v} C] [Abelian C] where
  /-- 底层过滤复形 -/
  FC : FilteredComplex C
  /-- 过滤有界 -/
  bnd : FC.IsBounded

/-- 有界过滤复形的范畴结构：作为过滤复形范畴的**全子范畴**
    （态射就是底层过滤复形之间的态射，有界性不参与态射的定义）。
    `comp` 用 lambda 直接定义，避免实例中 `≫` 的记法解析歧义。 -/
noncomputable instance : Category (BoundedFilteredComplex C) where
  Hom X Y := FilteredComplexMorphism X.FC Y.FC
  id X := 𝟙 X.FC
  comp {X Y Z} g h :=
    FilteredComplexMorphism.mk (fun k => g.f k ≫ h.f k)
      (fun k => by
        rw [Category.assoc, h.comm_d, ← Category.assoc, g.comm_d, Category.assoc])
      (fun s k =>
        ⟨(g.filt_compat s k).choose ≫ (h.filt_compat s k).choose, by
          rw [Category.assoc, (h.filt_compat s k).choose_spec,
            ← Category.assoc, (g.filt_compat s k).choose_spec, Category.assoc]⟩)
  id_comp {X Y} g :=
    FilteredComplexMorphism.ext (funext fun k => Category.id_comp (g.f k))
  comp_id {X Y} g :=
    FilteredComplexMorphism.ext (funext fun k => Category.comp_id (g.f k))
  assoc {W X Y Z} g h l :=
    FilteredComplexMorphism.ext (funext fun k => Category.assoc (g.f k) (h.f k) (l.f k))

/-! ### toSS 函子：有界过滤复形 ⥤ 谱序列 -/

/-- 通用提升引理：给定核层交换方块 `left ≫ f₂ = f₁ ≫ right`
    与 cokernel 投影层交换方块 `left ≫ πV₂ = πV₁ ≫ φ`，
    `imageSubobjectMap` 给出 `image(ker f₁ ≫ πV₁) → image(ker f₂ ≫ πV₂)`
    的提升使提升方块交换。 -/
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

/-- 辅助引理（保 Z 塔字段）：过滤复形态射诱导的关联分次映射
    把每个双次数 `(s, k)` 上的循环子对象 `Z_r` 映入目标谱序列的对应
    循环子对象（以 `∃` 提升使提升方块交换表述）。
    陈述为全真；证明体已清理。 -/
private theorem FilteredComplexMorphism.toSpectralSequenceMorphism_preserves_Z
    {X Y : BoundedFilteredComplex C} (g : X ⟶ Y) :
    ∀ (k : ℤ × ℤ) (r : WithTop ℕ),
    ∃ (lift : Subobject.underlying.obj
          (((X.FC.toSpectralSequence X.bnd).ssData k).Z r) ⟶
        Subobject.underlying.obj
          (((Y.FC.toSpectralSequence Y.bnd).ssData k).Z r)),
      lift ≫ (((Y.FC.toSpectralSequence Y.bnd).ssData k).Z r).arrow =
        (((X.FC.toSpectralSequence X.bnd).ssData k).Z r).arrow ≫
          FilteredComplexMorphism.assocGradedMap
            (g : FilteredComplexMorphism X.FC Y.FC) k.1 k.2 := by
  rintro ⟨s, k⟩ r
  -- 两边的谱序列都取自 toPreSS，ssData 即 toSSData，Z 即 cycleSubobject。
  dsimp only [FilteredComplex.toSpectralSequence, FilteredComplex.toPreSS]
  -- 提升族：源/目标在 s 与 s+1 层上的保过滤提升（.choose）。
  set u := (g.filt_compat s k).choose with hu
  set v := (g.filt_compat (s + 1) k).choose with hv
  set hu_spec := (g.filt_compat s k).choose_spec with hu_spec_def
  set hv_spec := (g.filt_compat (s + 1) k).choose_spec with hv_spec_def
  -- π₁：源关联分次层的 cokernel 投影。
  set π₁ := X.FC.filToAssocGraded s k with hπ₁
  -- π₂：目标关联分次层的 cokernel 投影。
  set π₂ := Y.FC.filToAssocGraded s k with hπ₂
  -- φ 的 π-性质：π₁ ≫ φ = u ≫ π₂。
  -- 这是 `assocGradedMap = cokernel.map ι₁ ι₂ v u w` 的定义性质
  -- （cokernel.map 是 cokernel.desc，π ≫ desc = 命名的映射）。
  have hφπ : π₁ ≫ FilteredComplexMorphism.assocGradedMap
      (g : FilteredComplexMorphism X.FC Y.FC) s k = u ≫ π₂ := by
    unfold FilteredComplexMorphism.assocGradedMap π₁ π₂
      FilteredComplex.filToAssocGraded
    exact cokernel.π_desc _ (u ≫ cokernel.π _) _
  -- f_r 依 r 分类：⊤ 时 f = F^s.arrow ≫ d（无第三分量），
  -- ↑n 时 f = F^s.arrow ≫ d ≫ cokernel.π (F^{s+n}(k-1)).arrow。
  -- 核心交换性：u ≫ f₂_基 = f₁_基 ≫ g.f (k-1)（f 基 = F^s.arrow ≫ d）。
  have key : u ≫ ((Y.FC.fil s k).arrow ≫ Y.FC.d k) =
      ((X.FC.fil s k).arrow ≫ X.FC.d k) ≫ g.f (k - 1) := by
    rw [← Category.assoc,
      show u ≫ (Y.FC.fil s k).arrow = (X.FC.fil s k).arrow ≫ g.f k by exact hu_spec,
      Category.assoc, g.comm_d]
    exact (Category.assoc _ _ _).symm
  -- r 分类：⊤ 时 f_r = F^s.arrow ≫ d（核层交换即 key）；
  -- ↑n 时 f_r = F^s.arrow ≫ d ≫ cokernel.π (F^{s+n}(k-1)).arrow，
  -- 右翼取 cokernel 层上由保过滤提升 w 诱导的 cokernel.map。
  rcases r with (_ | n)
  · dsimp only [FilteredComplex.toSSData, FilteredComplex.cycleSubobject]
    exact imageSubobjectMap_of_kernel_cokernel_square
      (left := u) (right := g.f (k - 1)) key hφπ.symm
  · dsimp only [FilteredComplex.toSSData, FilteredComplex.cycleSubobject]
    -- w：目标在 s+n 层（k-1 处）的保过滤提升。
    set w := (g.filt_compat (s + ↑n) (k - 1)).choose with hw
    have hwspec := (g.filt_compat (s + ↑n) (k - 1)).choose_spec
    -- cokernel 层诱导映射：coker(F_X^{s+n}) → coker(F_Y^{s+n})。
    set cok_right := cokernel.map ((X.FC.fil (s + ↑n) (k - 1)).arrow)
      ((Y.FC.fil (s + ↑n) (k - 1)).arrow) w (g.f (k - 1)) hwspec.symm with hcok
    have hπcok : cokernel.π ((X.FC.fil (s + ↑n) (k - 1)).arrow) ≫ cok_right =
        g.f (k - 1) ≫ cokernel.π ((Y.FC.fil (s + ↑n) (k - 1)).arrow) := by
      unfold cok_right at *
      exact cokernel.π_desc _ _ _
    -- 核层交换方块：u ≫ f₂_r = f₁_r ≫ cok_right。
    have hsq : u ≫ ((Y.FC.fil s k).arrow ≫ Y.FC.d k ≫
        cokernel.π ((Y.FC.fil (s + ↑n) (k - 1)).arrow)) =
      ((X.FC.fil s k).arrow ≫ X.FC.d k ≫
        cokernel.π ((X.FC.fil (s + ↑n) (k - 1)).arrow)) ≫ cok_right := by
      have e1 : u ≫ (Y.FC.fil s k).arrow = (X.FC.fil s k).arrow ≫ g.f k :=
        hu_spec
      have e2 : X.FC.d k ≫ g.f (k - 1) = g.f k ≫ Y.FC.d k := (g.comm_d k).symm
      -- e4：d ≫ (f ≫ π_Y) = d ≫ (π_X ≫ cok_right)（由 hπcok）。
      have e4 : X.FC.d k ≫ (g.f (k - 1) ≫
          cokernel.π ((Y.FC.fil (s + ↑n) (k - 1)).arrow)) =
          X.FC.d k ≫ (cokernel.π ((X.FC.fil (s + ↑n) (k - 1)).arrow) ≫ cok_right) := by
        rw [hπcok]
      calc u ≫ (Y.FC.fil s k).arrow ≫ Y.FC.d k ≫
          cokernel.π ((Y.FC.fil (s + ↑n) (k - 1)).arrow)
          = (u ≫ (Y.FC.fil s k).arrow) ≫ Y.FC.d k ≫
              cokernel.π ((Y.FC.fil (s + ↑n) (k - 1)).arrow) :=
            (Category.assoc _ _ _).symm
        _ = (X.FC.fil s k).arrow ≫ g.f k ≫ Y.FC.d k ≫
              cokernel.π ((Y.FC.fil (s + ↑n) (k - 1)).arrow) := by
            rw [← Category.assoc, e1, Category.assoc, Category.assoc]
        _ = (X.FC.fil s k).arrow ≫ X.FC.d k ≫ g.f (k - 1) ≫
              cokernel.π ((Y.FC.fil (s + ↑n) (k - 1)).arrow) := by
            -- hs：e2（d ≫ f = f ≫ d'）两侧各后接 π（显式用 assoc 抵消括号差）。
            have hs : (X.FC.fil s k).arrow ≫ g.f k ≫ Y.FC.d k ≫
                cokernel.π ((Y.FC.fil (s + ↑n) (k - 1)).arrow) =
                (X.FC.fil s k).arrow ≫ X.FC.d k ≫ g.f (k - 1) ≫
                  cokernel.π ((Y.FC.fil (s + ↑n) (k - 1)).arrow) := by
              have h : (g.f k ≫ Y.FC.d k) ≫ cokernel.π
                  ((Y.FC.fil (s + ↑n) (k - 1)).arrow) =
                  (X.FC.d k ≫ g.f (k - 1)) ≫ cokernel.π
                    ((Y.FC.fil (s + ↑n) (k - 1)).arrow) :=
                congrArg (fun x ↦ x ≫ cokernel.π
                  ((Y.FC.fil (s + ↑n) (k - 1)).arrow)) e2.symm
              calc (X.FC.fil s k).arrow ≫ g.f k ≫ Y.FC.d k ≫
                  cokernel.π ((Y.FC.fil (s + ↑n) (k - 1)).arrow)
                  = (X.FC.fil s k).arrow ≫ (g.f k ≫ Y.FC.d k) ≫ cokernel.π
                    ((Y.FC.fil (s + ↑n) (k - 1)).arrow) := by
                    rw [Category.assoc]
                _ = (X.FC.fil s k).arrow ≫ (X.FC.d k ≫ g.f (k - 1)) ≫
                    cokernel.π ((Y.FC.fil (s + ↑n) (k - 1)).arrow) := by
                  rw [h]
                _ = (X.FC.fil s k).arrow ≫ X.FC.d k ≫ g.f (k - 1) ≫
                    cokernel.π ((Y.FC.fil (s + ↑n) (k - 1)).arrow) := by
                  rw [Category.assoc]
            exact hs
        _ = (X.FC.fil s k).arrow ≫ X.FC.d k ≫ (cokernel.π
              ((X.FC.fil (s + ↑n) (k - 1)).arrow) ≫ cok_right) := by
            rw [e4]
        _ = ((X.FC.fil s k).arrow ≫ X.FC.d k ≫
              cokernel.π ((X.FC.fil (s + ↑n) (k - 1)).arrow)) ≫ cok_right := by
            rw [Category.assoc, Category.assoc, ← Category.assoc]
    exact imageSubobjectMap_of_kernel_cokernel_square
      (left := u) (right := cok_right) hsq hφπ.symm

/-- 辅助引理（保 B 塔字段）：过滤复形态射诱导的关联分次映射
    把每个双次数 `(s, k)` 上的边缘子对象 `B_r` 映入目标谱序列的对应
    边缘子对象（以 `∃` 提升使提升方块交换表述）。
    陈述为全真；证明体已清理。 -/
private theorem FilteredComplexMorphism.toSpectralSequenceMorphism_preserves_B
    {X Y : BoundedFilteredComplex C} (g : X ⟶ Y) :
    ∀ (k : ℤ × ℤ) (r : WithTop ℕ),
    ∃ (lift : Subobject.underlying.obj
          (((X.FC.toSpectralSequence X.bnd).ssData k).B r) ⟶
        Subobject.underlying.obj
          (((Y.FC.toSpectralSequence Y.bnd).ssData k).B r)),
      lift ≫ (((Y.FC.toSpectralSequence Y.bnd).ssData k).B r).arrow =
        (((X.FC.toSpectralSequence X.bnd).ssData k).B r).arrow ≫
          FilteredComplexMorphism.assocGradedMap
            (g : FilteredComplexMorphism X.FC Y.FC) k.1 k.2 := by
  rintro ⟨s, k⟩ r
  -- 两边的谱序列都取自 toPreSS，ssData 即 toSSData，B 即 boundarySubobject。
  dsimp only [FilteredComplex.toSpectralSequence, FilteredComplex.toPreSS]
  -- 提升族：s 层保过滤提升 u（源 F^s → 目标 F^s）。
  set u := (g.filt_compat s k).choose with hu
  set hu_spec := (g.filt_compat s k).choose_spec with hu_spec_def
  -- π₁/π₂：源/目标关联分次层的 cokernel 投影。
  set π₁ := X.FC.filToAssocGraded s k with hπ₁
  set π₂ := Y.FC.filToAssocGraded s k with hπ₂
  -- φ 的 π-性质：π₁ ≫ φ = u ≫ π₂（同 preserves_Z 的 hφπ）。
  have hφπ : π₁ ≫ FilteredComplexMorphism.assocGradedMap
      (g : FilteredComplexMorphism X.FC Y.FC) s k = u ≫ π₂ := by
    unfold FilteredComplexMorphism.assocGradedMap π₁ π₂
      FilteredComplex.filToAssocGraded
    exact cokernel.π_desc _ (u ≫ cokernel.π _) _
  -- s-n 层（k+1 处）源/目标的保过滤提升（imgD 层交换用）。
  -- B_r = imageSubobject(ofLE(I, F^s) ≫ πV)，其中 I = imgD ⊓ F^s，
  -- imgD = imageSubobject(F^{s-n+1}(k+1).arrow ≫ dToK k)（r=↑n）
  --   或 imageSubobject(dToK k)（r=⊤）。
  have hdToK : g.f (k + 1) ≫ Y.FC.dToK k = X.FC.dToK k ≫ g.f k := by
    let e : k + 1 - 1 = k := by omega
    have htr : g.f (k + 1 - 1) ≫ eqToHom (congrArg Y.FC.A e) =
        eqToHom (congrArg X.FC.A e) ≫ g.f k :=
      eqToHom_naturality (fun j => g.f j) e
    unfold FilteredComplex.dToK
    rw [← Category.assoc, g.comm_d (k + 1), Category.assoc, htr]
    simp only [Category.assoc]
  rcases r with (_ | n)
  · dsimp only [FilteredComplex.toSSData, FilteredComplex.boundarySubobject]
    let imgX := imageSubobject (X.FC.dToK k)
    let imgY := imageSubobject (Y.FC.dToK k)
    let IX := imgX ⊓ X.FC.fil s k
    let IY := imgY ⊓ Y.FC.fil s k
    let imgMap := imageSubobjectMap
      (Arrow.homMk' (g.f (k + 1)) (g.f k) hdToK)
    have himg : imgMap ≫ imgY.arrow = imgX.arrow ≫ g.f k := by
      exact imageSubobjectMap_arrow _
    have hIXimg : imgX.Factors IX.arrow :=
      Subobject.inf_arrow_factors_left _ _
    have hIXfil : (X.FC.fil s k).Factors IX.arrow :=
      Subobject.inf_arrow_factors_right _ _
    have hfacImg : imgY.Factors (IX.arrow ≫ g.f k) := by
      rw [← Subobject.factorThru_arrow _ _ hIXimg, Category.assoc, ← himg]
      exact Subobject.factors_of_factors_right _ (Subobject.factors_comp_arrow _)
    have hfacFil : (Y.FC.fil s k).Factors (IX.arrow ≫ g.f k) := by
      rw [← Subobject.factorThru_arrow _ _ hIXfil, Category.assoc, ← hu_spec]
      exact Subobject.factors_of_factors_right _ (Subobject.factors_comp_arrow _)
    have hfacI : IY.Factors (IX.arrow ≫ g.f k) := by
      rw [show IY = imgY ⊓ Y.FC.fil s k from rfl,
        Subobject.inf_factors]
      exact ⟨hfacImg, hfacFil⟩
    let α := IY.factorThru (IX.arrow ≫ g.f k) hfacI
    have hα : α ≫ IY.arrow = IX.arrow ≫ g.f k :=
      IY.factorThru_arrow _ hfacI
    have hmid : α ≫ Subobject.ofLE IY (Y.FC.fil s k) inf_le_right =
        Subobject.ofLE IX (X.FC.fil s k) inf_le_right ≫ u := by
      apply (cancel_mono (Y.FC.fil s k).arrow).mp
      calc
        (α ≫ Subobject.ofLE IY (Y.FC.fil s k) inf_le_right) ≫
            (Y.FC.fil s k).arrow = α ≫ IY.arrow := by
              rw [Category.assoc, Subobject.ofLE_arrow]
        _ = IX.arrow ≫ g.f k := hα
        _ = (Subobject.ofLE IX (X.FC.fil s k) inf_le_right ≫ u) ≫
            (Y.FC.fil s k).arrow := by
              rw [Category.assoc, hu_spec, ← Category.assoc, Subobject.ofLE_arrow]
    have hsq : α ≫ (Subobject.ofLE IY (Y.FC.fil s k) inf_le_right ≫ π₂) =
        (Subobject.ofLE IX (X.FC.fil s k) inf_le_right ≫ π₁) ≫
          FilteredComplexMorphism.assocGradedMap
            (g : FilteredComplexMorphism X.FC Y.FC) s k := by
      rw [← Category.assoc, hmid, Category.assoc, ← hφπ]
      simp only [Category.assoc]
    exact ⟨imageSubobjectMap (Arrow.homMk' α
      (FilteredComplexMorphism.assocGradedMap
        (g : FilteredComplexMorphism X.FC Y.FC) s k) hsq),
      imageSubobjectMap_arrow _⟩
  · dsimp only [FilteredComplex.toSSData, FilteredComplex.boundarySubobject]
    let a : ℤ := s - (n : ℤ) + 1
    let q := (g.filt_compat a (k + 1)).choose
    have hqspec : q ≫ (Y.FC.fil a (k + 1)).arrow =
        (X.FC.fil a (k + 1)).arrow ≫ g.f (k + 1) :=
      (g.filt_compat a (k + 1)).choose_spec
    have hgen : q ≫ ((Y.FC.fil a (k + 1)).arrow ≫ Y.FC.dToK k) =
        ((X.FC.fil a (k + 1)).arrow ≫ X.FC.dToK k) ≫ g.f k := by
      rw [← Category.assoc, hqspec, Category.assoc, hdToK]
      simp only [Category.assoc]
    let imgX := imageSubobject
      ((X.FC.fil a (k + 1)).arrow ≫ X.FC.dToK k)
    let imgY := imageSubobject
      ((Y.FC.fil a (k + 1)).arrow ≫ Y.FC.dToK k)
    let IX := imgX ⊓ X.FC.fil s k
    let IY := imgY ⊓ Y.FC.fil s k
    let imgMap := imageSubobjectMap (Arrow.homMk' q (g.f k) hgen)
    have himg : imgMap ≫ imgY.arrow = imgX.arrow ≫ g.f k := by
      exact imageSubobjectMap_arrow _
    have hIXimg : imgX.Factors IX.arrow :=
      Subobject.inf_arrow_factors_left _ _
    have hIXfil : (X.FC.fil s k).Factors IX.arrow :=
      Subobject.inf_arrow_factors_right _ _
    have hfacImg : imgY.Factors (IX.arrow ≫ g.f k) := by
      rw [← Subobject.factorThru_arrow _ _ hIXimg, Category.assoc, ← himg]
      exact Subobject.factors_of_factors_right _ (Subobject.factors_comp_arrow _)
    have hfacFil : (Y.FC.fil s k).Factors (IX.arrow ≫ g.f k) := by
      rw [← Subobject.factorThru_arrow _ _ hIXfil, Category.assoc, ← hu_spec]
      exact Subobject.factors_of_factors_right _ (Subobject.factors_comp_arrow _)
    have hfacI : IY.Factors (IX.arrow ≫ g.f k) := by
      rw [show IY = imgY ⊓ Y.FC.fil s k from rfl,
        Subobject.inf_factors]
      exact ⟨hfacImg, hfacFil⟩
    let α := IY.factorThru (IX.arrow ≫ g.f k) hfacI
    have hα : α ≫ IY.arrow = IX.arrow ≫ g.f k :=
      IY.factorThru_arrow _ hfacI
    have hmid : α ≫ Subobject.ofLE IY (Y.FC.fil s k) inf_le_right =
        Subobject.ofLE IX (X.FC.fil s k) inf_le_right ≫ u := by
      apply (cancel_mono (Y.FC.fil s k).arrow).mp
      calc
        (α ≫ Subobject.ofLE IY (Y.FC.fil s k) inf_le_right) ≫
            (Y.FC.fil s k).arrow = α ≫ IY.arrow := by
              rw [Category.assoc, Subobject.ofLE_arrow]
        _ = IX.arrow ≫ g.f k := hα
        _ = (Subobject.ofLE IX (X.FC.fil s k) inf_le_right ≫ u) ≫
            (Y.FC.fil s k).arrow := by
              rw [Category.assoc, hu_spec, ← Category.assoc, Subobject.ofLE_arrow]
    have hsq : α ≫ (Subobject.ofLE IY (Y.FC.fil s k) inf_le_right ≫ π₂) =
        (Subobject.ofLE IX (X.FC.fil s k) inf_le_right ≫ π₁) ≫
          FilteredComplexMorphism.assocGradedMap
            (g : FilteredComplexMorphism X.FC Y.FC) s k := by
      rw [← Category.assoc, hmid, Category.assoc, ← hφπ]
      simp only [Category.assoc]
    exact ⟨imageSubobjectMap (Arrow.homMk' α
      (FilteredComplexMorphism.assocGradedMap
        (g : FilteredComplexMorphism X.FC Y.FC) s k) hsq),
      imageSubobjectMap_arrow _⟩

/-- 过滤复形态射在第 `n` 页诱导的真实页映射。它同时使用已经证明的
    `Z_n` 与 `B_n` 提升，并由 cokernel 的函子性下降到 `Z_n/B_n`。 -/
noncomputable def FilteredComplexMorphism.inducedPageMap
    {X Y : BoundedFilteredComplex C} (g : X ⟶ Y)
    (n : ℕ) (s k : ℤ) :
    (X.FC.toSSData X.bnd s k).page (↑n) ⟶
      (Y.FC.toSSData Y.bnd s k).page (↑n) := by
  let hB := FilteredComplexMorphism.toSpectralSequenceMorphism_preserves_B
    g (s, k) (↑n)
  let hZ := FilteredComplexMorphism.toSpectralSequenceMorphism_preserves_Z
    g (s, k) (↑n)
  have hBspec := hB.choose_spec
  have hZspec := hZ.choose_spec
  change hB.choose ≫ ((Y.FC.toSSData Y.bnd s k).B (↑n)).arrow =
    ((X.FC.toSSData X.bnd s k).B (↑n)).arrow ≫
      FilteredComplexMorphism.assocGradedMap
        (g : FilteredComplexMorphism X.FC Y.FC) s k at hBspec
  change hZ.choose ≫ ((Y.FC.toSSData Y.bnd s k).Z (↑n)).arrow =
    ((X.FC.toSSData X.bnd s k).Z (↑n)).arrow ≫
      FilteredComplexMorphism.assocGradedMap
        (g : FilteredComplexMorphism X.FC Y.FC) s k at hZspec
  exact cokernel.map
    (Subobject.ofLE ((X.FC.toSSData X.bnd s k).B (↑n))
      ((X.FC.toSSData X.bnd s k).Z (↑n))
      ((X.FC.toSSData X.bnd s k).B_le_Z (↑n)))
    (Subobject.ofLE ((Y.FC.toSSData Y.bnd s k).B (↑n))
      ((Y.FC.toSSData Y.bnd s k).Z (↑n))
      ((Y.FC.toSSData Y.bnd s k).B_le_Z (↑n)))
    hB.choose hZ.choose (by
      apply (cancel_mono (((Y.FC.toSSData Y.bnd s k).Z (↑n)).arrow)).mp
      simp only [Category.assoc, Subobject.ofLE_arrow]
      rw [hZspec, ← Category.assoc, hBspec,
        Subobject.ofLE_arrow])

/-- 诱导页映射与页投影相容。 -/
theorem FilteredComplexMorphism.pageπ_inducedPageMap
    {X Y : BoundedFilteredComplex C} (g : X ⟶ Y)
    (n : ℕ) (s k : ℤ) :
    (X.FC.toSSData X.bnd s k).pageπ (↑n) ≫
        FilteredComplexMorphism.inducedPageMap g n s k =
      (FilteredComplexMorphism.toSpectralSequenceMorphism_preserves_Z
        g (s, k) (↑n)).choose ≫
        (Y.FC.toSSData Y.bnd s k).pageπ (↑n) := by
  unfold FilteredComplexMorphism.inducedPageMap SSData.pageπ
  exact cokernel.π_desc _ _ _

/-- 诱导页映射与过滤复形谱序列的第 `n` 页微分交换。证明在源循环的
    核代表元上比较两条路径，再依次消去像分解与页投影两个满态射。 -/
theorem FilteredComplexMorphism.inducedPageMap_comm_pageDifferential
    {X Y : BoundedFilteredComplex C} (g : X ⟶ Y)
    (n : ℕ) (s k : ℤ) :
    FilteredComplexMorphism.inducedPageMap g n s k ≫
        Y.FC.pageDifferential Y.bnd s k n =
      X.FC.pageDifferential X.bnd s k n ≫
        FilteredComplexMorphism.inducedPageMap g n (s + (n : ℤ)) (k - 1) := by
  classical
  let fX := (X.FC.fil s k).arrow ≫ X.FC.d k ≫
    cokernel.π ((X.FC.fil (s + (n : ℤ)) (k - 1)).arrow)
  let fY := (Y.FC.fil s k).arrow ≫ Y.FC.d k ≫
    cokernel.π ((Y.FC.fil (s + (n : ℤ)) (k - 1)).arrow)
  let KX := kernelSubobject fX
  let KY := kernelSubobject fY
  let πX := X.FC.filToAssocGraded s k
  let πY := Y.FC.filToAssocGraded s k
  let ZX := imageSubobject (KX.arrow ≫ πX)
  let ZY := imageSubobject (KY.arrow ≫ πY)
  let qX := factorThruImageSubobject (KX.arrow ≫ πX)
  let u := (g.filt_compat s k).choose
  have huspec : u ≫ (Y.FC.fil s k).arrow =
      (X.FC.fil s k).arrow ≫ g.f k :=
    (g.filt_compat s k).choose_spec
  let w := (g.filt_compat (s + (n : ℤ)) (k - 1)).choose
  have hwspec : w ≫ (Y.FC.fil (s + (n : ℤ)) (k - 1)).arrow =
      (X.FC.fil (s + (n : ℤ)) (k - 1)).arrow ≫ g.f (k - 1) :=
    (g.filt_compat (s + (n : ℤ)) (k - 1)).choose_spec
  have hφs : πX ≫ FilteredComplexMorphism.assocGradedMap
      (g : FilteredComplexMorphism X.FC Y.FC) s k = u ≫ πY := by
    unfold FilteredComplexMorphism.assocGradedMap πX πY
      FilteredComplex.filToAssocGraded
    exact cokernel.π_desc _ _ _
  let cokT := cokernel.map
    ((X.FC.fil (s + (n : ℤ)) (k - 1)).arrow)
    ((Y.FC.fil (s + (n : ℤ)) (k - 1)).arrow)
    w (g.f (k - 1)) hwspec.symm
  have hcokT : cokernel.π ((X.FC.fil (s + (n : ℤ)) (k - 1)).arrow) ≫ cokT =
      g.f (k - 1) ≫
        cokernel.π ((Y.FC.fil (s + (n : ℤ)) (k - 1)).arrow) := by
    unfold cokT
    exact cokernel.π_desc _ _ _
  have hkernel : u ≫ fY = fX ≫ cokT := by
    dsimp only [fX, fY]
    calc
      u ≫ (Y.FC.fil s k).arrow ≫ Y.FC.d k ≫
          cokernel.π ((Y.FC.fil (s + (n : ℤ)) (k - 1)).arrow) =
        (X.FC.fil s k).arrow ≫ g.f k ≫ Y.FC.d k ≫
          cokernel.π ((Y.FC.fil (s + (n : ℤ)) (k - 1)).arrow) := by
            rw [← Category.assoc, huspec]
            simp only [Category.assoc]
      _ = (X.FC.fil s k).arrow ≫ X.FC.d k ≫ g.f (k - 1) ≫
          cokernel.π ((Y.FC.fil (s + (n : ℤ)) (k - 1)).arrow) := by
            simpa only [Category.assoc] using congrArg
              (fun h => (X.FC.fil s k).arrow ≫ h ≫
                cokernel.π ((Y.FC.fil (s + (n : ℤ)) (k - 1)).arrow))
              (g.comm_d k)
      _ = (X.FC.fil s k).arrow ≫ X.FC.d k ≫
          cokernel.π ((X.FC.fil (s + (n : ℤ)) (k - 1)).arrow) ≫ cokT := by
            rw [hcokT]
      _ = ((X.FC.fil s k).arrow ≫ X.FC.d k ≫
          cokernel.π ((X.FC.fil (s + (n : ℤ)) (k - 1)).arrow)) ≫ cokT := by
            simp only [Category.assoc]
  let kerMap := kernelSubobjectMap
    (Arrow.homMk (f := Arrow.mk fX) (g := Arrow.mk fY) u cokT hkernel)
  have hkerMap : kerMap ≫ KY.arrow = KX.arrow ≫ u := by
    exact kernelSubobjectMap_arrow _
  let qY := kerMap ≫ factorThruImageSubobject (KY.arrow ≫ πY)
  let zmapS := (FilteredComplexMorphism.toSpectralSequenceMorphism_preserves_Z
    g (s, k) (↑n)).choose
  have hqX : qX ≫ ZX.arrow = KX.arrow ≫ πX := by
    simp only [qX, ZX, imageSubobject_arrow_comp]
  have hqY : qY ≫ ZY.arrow = KX.arrow ≫ u ≫ πY := by
    calc
      qY ≫ ZY.arrow = (kerMap ≫ KY.arrow) ≫ πY := by
        simp only [qY, ZY, Category.assoc, imageSubobject_arrow_comp]
      _ = (KX.arrow ≫ u) ≫ πY := by rw [hkerMap]
      _ = KX.arrow ≫ u ≫ πY := by simp only [Category.assoc]
  have hzmapS : qX ≫ zmapS = qY := by
    apply (cancel_mono ZY.arrow).mp
    have hzspec := (FilteredComplexMorphism.toSpectralSequenceMorphism_preserves_Z
      g (s, k) (↑n)).choose_spec
    change zmapS ≫ ZY.arrow = ZX.arrow ≫
      FilteredComplexMorphism.assocGradedMap
        (g : FilteredComplexMorphism X.FC Y.FC) s k at hzspec
    calc
      (qX ≫ zmapS) ≫ ZY.arrow = qX ≫ ZX.arrow ≫
          FilteredComplexMorphism.assocGradedMap
            (g : FilteredComplexMorphism X.FC Y.FC) s k := by
              rw [Category.assoc, hzspec]
      _ = KX.arrow ≫ πX ≫
          FilteredComplexMorphism.assocGradedMap
            (g : FilteredComplexMorphism X.FC Y.FC) s k := by
              simpa only [Category.assoc] using congrArg
                (fun h => h ≫ FilteredComplexMorphism.assocGradedMap
                  (g : FilteredComplexMorphism X.FC Y.FC) s k) hqX
      _ = KX.arrow ≫ u ≫ πY := by rw [hφs]
      _ = qY ≫ ZY.arrow := hqY.symm
  let vX := Abelian.monoLift (X.FC.fil (s + (n : ℤ)) (k - 1)).arrow
    (KX.arrow ≫ (X.FC.fil s k).arrow ≫ X.FC.d k)
    (by simpa only [fX, Category.assoc] using kernelSubobject_arrow_comp fX)
  have hvX : vX ≫ (X.FC.fil (s + (n : ℤ)) (k - 1)).arrow =
      KX.arrow ≫ (X.FC.fil s k).arrow ≫ X.FC.d k :=
    Abelian.monoLift_comp _ _ _
  let vY := vX ≫ w
  have hvY : kerMap ≫ KY.arrow ≫ (Y.FC.fil s k).arrow ≫ Y.FC.d k =
      vY ≫ (Y.FC.fil (s + (n : ℤ)) (k - 1)).arrow := by
    calc
      kerMap ≫ KY.arrow ≫ (Y.FC.fil s k).arrow ≫ Y.FC.d k =
          KX.arrow ≫ u ≫ (Y.FC.fil s k).arrow ≫ Y.FC.d k := by
            simpa only [Category.assoc] using congrArg
              (fun h => h ≫ (Y.FC.fil s k).arrow ≫ Y.FC.d k) hkerMap
      _ = KX.arrow ≫ (X.FC.fil s k).arrow ≫ g.f k ≫ Y.FC.d k := by
            simpa only [Category.assoc] using congrArg
              (fun h => KX.arrow ≫ h ≫ Y.FC.d k) huspec
      _ = KX.arrow ≫ (X.FC.fil s k).arrow ≫ X.FC.d k ≫ g.f (k - 1) := by
            simpa only [Category.assoc] using congrArg
              (fun h => KX.arrow ≫ (X.FC.fil s k).arrow ≫ h) (g.comm_d k)
      _ = vX ≫ (X.FC.fil (s + (n : ℤ)) (k - 1)).arrow ≫ g.f (k - 1) := by
            simpa only [Category.assoc] using congrArg
              (fun h => h ≫ g.f (k - 1)) hvX.symm
      _ = vX ≫ w ≫ (Y.FC.fil (s + (n : ℤ)) (k - 1)).arrow := by
            simpa only [Category.assoc] using congrArg (fun h => vX ≫ h) hwspec.symm
      _ = vY ≫ (Y.FC.fil (s + (n : ℤ)) (k - 1)).arrow := by
            simp only [vY, Category.assoc]
  let gX := (X.FC.fil (s + (n : ℤ)) (k - 1)).arrow ≫ X.FC.d (k - 1) ≫
    cokernel.π ((X.FC.fil (s + (n : ℤ) + (n : ℤ)) (k - 1 - 1)).arrow)
  let gY := (Y.FC.fil (s + (n : ℤ)) (k - 1)).arrow ≫ Y.FC.d (k - 1) ≫
    cokernel.π ((Y.FC.fil (s + (n : ℤ) + (n : ℤ)) (k - 1 - 1)).arrow)
  have hvgX : vX ≫ gX = 0 := by
    dsimp only [gX]
    calc
      vX ≫ (X.FC.fil (s + (n : ℤ)) (k - 1)).arrow ≫ X.FC.d (k - 1) ≫
          cokernel.π ((X.FC.fil (s + (n : ℤ) + (n : ℤ)) (k - 1 - 1)).arrow) =
        (KX.arrow ≫ (X.FC.fil s k).arrow ≫ X.FC.d k) ≫ X.FC.d (k - 1) ≫
          cokernel.π ((X.FC.fil (s + (n : ℤ) + (n : ℤ)) (k - 1 - 1)).arrow) := by
            simpa only [Category.assoc] using congrArg
              (fun h => h ≫ X.FC.d (k - 1) ≫
                cokernel.π
                  ((X.FC.fil (s + (n : ℤ) + (n : ℤ)) (k - 1 - 1)).arrow)) hvX
      _ = 0 := by
        simpa only [Category.assoc, comp_zero, zero_comp] using congrArg
          (fun h => KX.arrow ≫ (X.FC.fil s k).arrow ≫ h ≫
            cokernel.π
              ((X.FC.fil (s + (n : ℤ) + (n : ℤ)) (k - 1 - 1)).arrow))
          (X.FC.d_comp_d k)
  have hvgY : vY ≫ gY = 0 := by
    dsimp only [gY]
    calc
      vY ≫ (Y.FC.fil (s + (n : ℤ)) (k - 1)).arrow ≫ Y.FC.d (k - 1) ≫
          cokernel.π ((Y.FC.fil (s + (n : ℤ) + (n : ℤ)) (k - 1 - 1)).arrow) =
        (kerMap ≫ KY.arrow ≫ (Y.FC.fil s k).arrow ≫ Y.FC.d k) ≫
          Y.FC.d (k - 1) ≫
          cokernel.π ((Y.FC.fil (s + (n : ℤ) + (n : ℤ)) (k - 1 - 1)).arrow) := by
            simpa only [Category.assoc] using congrArg
              (fun h => h ≫ Y.FC.d (k - 1) ≫
                cokernel.π
                  ((Y.FC.fil (s + (n : ℤ) + (n : ℤ)) (k - 1 - 1)).arrow)) hvY.symm
      _ = 0 := by
        simpa only [Category.assoc, comp_zero, zero_comp] using congrArg
          (fun h => kerMap ≫ KY.arrow ≫ (Y.FC.fil s k).arrow ≫ h ≫
            cokernel.π
              ((Y.FC.fil (s + (n : ℤ) + (n : ℤ)) (k - 1 - 1)).arrow))
          (Y.FC.d_comp_d k)
  let KX' := kernelSubobject gX
  let KY' := kernelSubobject gY
  let πX' := X.FC.filToAssocGraded (s + (n : ℤ)) (k - 1)
  let πY' := Y.FC.filToAssocGraded (s + (n : ℤ)) (k - 1)
  let qX' := factorThruKernelSubobject gX vX hvgX ≫
    factorThruImageSubobject (KX'.arrow ≫ πX')
  let qY' := factorThruKernelSubobject gY vY hvgY ≫
    factorThruImageSubobject (KY'.arrow ≫ πY')
  let ZX' := imageSubobject (KX'.arrow ≫ πX')
  let ZY' := imageSubobject (KY'.arrow ≫ πY')
  let zmapT := (FilteredComplexMorphism.toSpectralSequenceMorphism_preserves_Z
    g (s + (n : ℤ), k - 1) (↑n)).choose
  have hqX' : qX' ≫ ZX'.arrow = vX ≫ πX' := by
    dsimp only [qX', ZX']
    rw [Category.assoc, imageSubobject_arrow_comp, ← Category.assoc,
      factorThruKernelSubobject_comp_arrow]
  have hqY' : qY' ≫ ZY'.arrow = vX ≫ w ≫ πY' := by
    dsimp only [qY', ZY']
    rw [Category.assoc, imageSubobject_arrow_comp, ← Category.assoc,
      factorThruKernelSubobject_comp_arrow]
    simp only [vY, Category.assoc]
  have hzmapT : qX' ≫ zmapT = qY' := by
    apply (cancel_mono ZY'.arrow).mp
    have hzspec := (FilteredComplexMorphism.toSpectralSequenceMorphism_preserves_Z
      g (s + (n : ℤ), k - 1) (↑n)).choose_spec
    change zmapT ≫ ZY'.arrow = ZX'.arrow ≫
        FilteredComplexMorphism.assocGradedMap
          (g : FilteredComplexMorphism X.FC Y.FC) (s + (n : ℤ)) (k - 1) at hzspec
    have hφt : πX' ≫ FilteredComplexMorphism.assocGradedMap
        (g : FilteredComplexMorphism X.FC Y.FC) (s + (n : ℤ)) (k - 1) =
        w ≫ πY' := by
      unfold FilteredComplexMorphism.assocGradedMap πX' πY'
        FilteredComplex.filToAssocGraded
      exact cokernel.π_desc _ _ _
    calc
      (qX' ≫ zmapT) ≫
          ZY'.arrow =
        qX' ≫ ZX'.arrow ≫
          FilteredComplexMorphism.assocGradedMap
            (g : FilteredComplexMorphism X.FC Y.FC) (s + (n : ℤ)) (k - 1) := by
              rw [Category.assoc, hzspec]
      _ = vX ≫ πX' ≫ FilteredComplexMorphism.assocGradedMap
          (g : FilteredComplexMorphism X.FC Y.FC) (s + (n : ℤ)) (k - 1) := by
            simpa only [Category.assoc] using congrArg
              (fun h => h ≫ FilteredComplexMorphism.assocGradedMap
                (g : FilteredComplexMorphism X.FC Y.FC)
                (s + (n : ℤ)) (k - 1)) hqX'
      _ = vX ≫ w ≫ πY' := by rw [hφt]
      _ = qY' ≫ ZY'.arrow := hqY'.symm
  haveI : Epi ((X.FC.toSSData X.bnd s k).pageπ (↑n)) := by
    unfold SSData.pageπ
    infer_instance
  apply (cancel_epi ((X.FC.toSSData X.bnd s k).pageπ (↑n))).mp
  apply (cancel_epi qX).mp
  have hY := Y.FC.pageDifferential_on_kernel Y.bnd s k n kerMap vY hvY hvgY
  have hX := X.FC.pageDifferential_on_kernel X.bnd s k n
    (𝟙 (Subobject.underlying.obj KX)) vX
    (by simpa only [Category.id_comp] using hvX.symm) hvgX
  change qY ≫ (Y.FC.toSSData Y.bnd s k).pageπ (↑n) ≫
      Y.FC.pageDifferential Y.bnd s k n =
    qY' ≫ (Y.FC.toSSData Y.bnd (s + (n : ℤ)) (k - 1)).pageπ (↑n) at hY
  change ((𝟙 (Subobject.underlying.obj KX)) ≫ qX) ≫
      (X.FC.toSSData X.bnd s k).pageπ (↑n) ≫
      X.FC.pageDifferential X.bnd s k n =
    qX' ≫ (X.FC.toSSData X.bnd (s + (n : ℤ)) (k - 1)).pageπ (↑n) at hX
  simp only [Category.id_comp] at hX
  have hPageS := FilteredComplexMorphism.pageπ_inducedPageMap g n s k
  have hPageT := FilteredComplexMorphism.pageπ_inducedPageMap
    g n (s + (n : ℤ)) (k - 1)
  calc
    qX ≫ (X.FC.toSSData X.bnd s k).pageπ (↑n) ≫
        FilteredComplexMorphism.inducedPageMap g n s k ≫
        Y.FC.pageDifferential Y.bnd s k n =
      qX ≫ zmapS ≫ (Y.FC.toSSData Y.bnd s k).pageπ (↑n) ≫
        Y.FC.pageDifferential Y.bnd s k n := by
          simpa only [Category.assoc] using congrArg
            (fun h => qX ≫ h ≫ Y.FC.pageDifferential Y.bnd s k n) hPageS
    _ = qY ≫ (Y.FC.toSSData Y.bnd s k).pageπ (↑n) ≫
        Y.FC.pageDifferential Y.bnd s k n := by
          simpa only [Category.assoc] using congrArg
            (fun h => h ≫ (Y.FC.toSSData Y.bnd s k).pageπ (↑n) ≫
              Y.FC.pageDifferential Y.bnd s k n) hzmapS
    _ = qY' ≫ (Y.FC.toSSData Y.bnd (s + (n : ℤ)) (k - 1)).pageπ (↑n) := by
          simpa only [Category.assoc] using hY
    _ = qX' ≫ zmapT ≫
        (Y.FC.toSSData Y.bnd (s + (n : ℤ)) (k - 1)).pageπ (↑n) := by
          simpa only [Category.assoc] using congrArg
            (fun h => h ≫
              (Y.FC.toSSData Y.bnd (s + (n : ℤ)) (k - 1)).pageπ (↑n))
            hzmapT.symm
    _ = qX' ≫ (X.FC.toSSData X.bnd (s + (n : ℤ)) (k - 1)).pageπ (↑n) ≫
        FilteredComplexMorphism.inducedPageMap g n (s + (n : ℤ)) (k - 1) := by
          simpa only [Category.assoc] using congrArg (fun h => qX' ≫ h) hPageT.symm
    _ = qX ≫ (X.FC.toSSData X.bnd s k).pageπ (↑n) ≫
        X.FC.pageDifferential X.bnd s k n ≫
        FilteredComplexMorphism.inducedPageMap g n (s + (n : ℤ)) (k - 1) := by
          simpa only [Category.assoc] using congrArg
            (fun h => h ≫
              FilteredComplexMorphism.inducedPageMap g n (s + (n : ℤ)) (k - 1))
            hX.symm

/-- 有界过滤复形态射在底层 `SSData` 族上诱导的态射。 -/
private noncomputable def FilteredComplexMorphism.toSSDataMorphism
    {X Y : BoundedFilteredComplex C} (g : X ⟶ Y) :
    SSDataMorphism (ℤ × ℤ)
      (X.FC.toSpectralSequence X.bnd).ssData
      (Y.FC.toSpectralSequence Y.bnd).ssData where
  φ := fun ⟨s, k⟩ => FilteredComplexMorphism.assocGradedMap
    (g : FilteredComplexMorphism X.FC Y.FC) s k
  preserves_Z := FilteredComplexMorphism.toSpectralSequenceMorphism_preserves_Z g
  preserves_B := FilteredComplexMorphism.toSpectralSequenceMorphism_preserves_B g

/-- `SSDataMorphism` 给出的规范页态射等于此前构造的第 `n` 页态射。 -/
private theorem FilteredComplexMorphism.pageMap_eq_inducedPageMap
    {X Y : BoundedFilteredComplex C} (g : X ⟶ Y)
    (n : ℕ) (s k : ℤ) :
    (FilteredComplexMorphism.toSSDataMorphism g).pageMap (s, k) (↑n) =
      FilteredComplexMorphism.inducedPageMap g n s k := by
  rfl

/-- 辅助引理（微分交换字段）：由底层映射规范诱导出的页态射与页微分
    交换。非负页使用诱导页映射自然性；负页的微分按定义为零。 -/
private theorem FilteredComplexMorphism.toSpectralSequenceMorphism_comm_d
    {X Y : BoundedFilteredComplex C} (g : X ⟶ Y) :
    ∀ (r : ℤ) (k : ℤ × ℤ),
      let n : WithTop ℕ :=
        ↑(r - (X.FC.toSpectralSequence X.bnd).r₀).toNat
      (FilteredComplexMorphism.toSSDataMorphism g).pageMap k n ≫
          (Y.FC.toSpectralSequence Y.bnd).d r k =
        (X.FC.toSpectralSequence X.bnd).d r k ≫
          (FilteredComplexMorphism.toSSDataMorphism g).pageMap
            (k + (X.FC.toSpectralSequence X.bnd).diffDeg r) n := by
  intro r ⟨s, k⟩
  dsimp only
  by_cases hr : 0 ≤ r
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hr
    change (FilteredComplexMorphism.toSSDataMorphism g).pageMap
          (s, k) (↑n) ≫ (Y.FC.toPreSS Y.bnd).d (↑n) (s, k) =
      (X.FC.toPreSS X.bnd).d (↑n) (s, k) ≫
        (FilteredComplexMorphism.toSSDataMorphism g).pageMap
          (s + (n : ℤ), k - 1) (↑n)
    rw [FilteredComplexMorphism.pageMap_eq_inducedPageMap g n s k,
      FilteredComplexMorphism.pageMap_eq_inducedPageMap g n
        (s + (n : ℤ)) (k - 1)]
    change FilteredComplexMorphism.inducedPageMap g n s k ≫
        (Y.FC.toPreSS Y.bnd).d (↑n) (s, k) =
      (X.FC.toPreSS X.bnd).d (↑n) (s, k) ≫
        FilteredComplexMorphism.inducedPageMap g n (s + (n : ℤ)) (k - 1)
    simpa [FilteredComplex.toPreSS] using
      FilteredComplexMorphism.inducedPageMap_comm_pageDifferential g n s k
  · change _ ≫ (Y.FC.toPreSS Y.bnd).d r (s, k) =
      (X.FC.toPreSS X.bnd).d r (s, k) ≫ _
    dsimp only [FilteredComplex.toPreSS]
    simp only [dif_neg hr, comp_zero, zero_comp]

/-- 过滤复形态射在有界性下诱导的**谱序列态射**。
    `φ k := assocGradedMap`（关联分次上映射，经由 `filt_compat` 提升由
    `cokernel.map` 构造）；保 Z / 保 B / 与 d 交换分别引用上方辅助引理。 -/
noncomputable def FilteredComplexMorphism.toSpectralSequenceMorphism
    {X Y : BoundedFilteredComplex C} (g : X ⟶ Y) :
    X.FC.toSpectralSequence X.bnd ⟶ Y.FC.toSpectralSequence Y.bnd where
  toSSDataMorphism := FilteredComplexMorphism.toSSDataMorphism g
  r₀_eq := rfl
  diffDeg_eq := rfl
  comm_d := by
    intro r k
    dsimp only
    simp only [SSDataMorphism.pageMapOfEq, eqToHom_refl, Category.comp_id]
    exact FilteredComplexMorphism.toSpectralSequenceMorphism_comm_d g r k

/-- 恒等过滤复形态射诱导恒等谱序列态射（φ 分量为关联分次上的恒等）。 -/
theorem FilteredComplexMorphism.toSpectralSequenceMorphism_id
    (X : BoundedFilteredComplex C) :
    (FilteredComplexMorphism.toSpectralSequenceMorphism (𝟙 X)).φ =
      fun _ => 𝟙 _ := by
  funext ⟨s, k⟩
  exact FilteredComplexMorphism.assocGradedMap_id X.FC s k

/-- 复合过滤复形态射在关联分次上映射的复合性：
    复合态射的 `assocGradedMap` 等于两次 `assocGradedMap` 的复合。
    先经桥接引理转成广义版本，再把复合态射的 choose 提升
    （等于两次提升的复合，由 `cancel_mono arrow` 论证）替换为复合提升，
    最后调用广义复合引理。 -/
theorem FilteredComplexMorphism.assocGradedMap_comp
    {FC₁ FC₂ FC₃ : FilteredComplex C}
    (g : FilteredComplexMorphism FC₁ FC₂) (h : FilteredComplexMorphism FC₂ FC₃)
    (s k : ℤ) :
    (FilteredComplexMorphism.comp g h).assocGradedMap s k =
      g.assocGradedMap s k ≫ h.assocGradedMap s k := by
  rw [FilteredComplexMorphism.assocGradedMap_eq (FilteredComplexMorphism.comp g h),
    g.assocGradedMap_eq, h.assocGradedMap_eq]
  have hlift : (fun s k : ℤ =>
        ((FilteredComplexMorphism.comp g h).filt_compat s k).choose) =
      fun s k => (g.filt_compat s k).choose ≫ (h.filt_compat s k).choose := by
    funext s k
    apply (cancel_mono ((FC₃.fil s k).arrow)).mp
    rw [Category.assoc _ _ ((FC₃.fil s k).arrow),
      ((FilteredComplexMorphism.comp g h).filt_compat s k).choose_spec,
      (h.filt_compat s k).choose_spec]
    conv_rhs =>
      rw [← Category.assoc _ _ (h.f k), (g.filt_compat s k).choose_spec]
    exact (Category.assoc _ _ _).symm
  -- g 与 h 各自的提升方块（形如 `assocGradedMap_eq` 中的 hw 证明）。
  have hwg : ∀ (s k : ℤ),
      Subobject.ofLE (FC₁.fil (s + 1) k) (FC₁.fil s k) (FC₁.fil_anti s k) ≫
          (g.filt_compat s k).choose =
        (g.filt_compat (s + 1) k).choose ≫
          Subobject.ofLE (FC₂.fil (s + 1) k) (FC₂.fil s k) (FC₂.fil_anti s k) := by
    intro s k
    apply (cancel_mono ((FC₂.fil s k).arrow)).mp
    simp only [Category.assoc, Subobject.ofLE_arrow]
    rw [(g.filt_compat s k).choose_spec, (g.filt_compat (s + 1) k).choose_spec,
      ← Category.assoc, Subobject.ofLE_arrow]
  have hwh : ∀ (s k : ℤ),
      Subobject.ofLE (FC₂.fil (s + 1) k) (FC₂.fil s k) (FC₂.fil_anti s k) ≫
          (h.filt_compat s k).choose =
        (h.filt_compat (s + 1) k).choose ≫
          Subobject.ofLE (FC₃.fil (s + 1) k) (FC₃.fil s k) (FC₃.fil_anti s k) := by
    intro s k
    apply (cancel_mono ((FC₃.fil s k).arrow)).mp
    simp only [Category.assoc, Subobject.ofLE_arrow]
    rw [(h.filt_compat s k).choose_spec, (h.filt_compat (s + 1) k).choose_spec,
      ← Category.assoc, Subobject.ofLE_arrow]
  -- 复合提升方块：g、h 的两个方块沿中间层的 ofLE₂ 拼接而成。
  have hwφ : ∀ (s k : ℤ),
      Subobject.ofLE (FC₁.fil (s + 1) k) (FC₁.fil s k) (FC₁.fil_anti s k) ≫
          ((g.filt_compat s k).choose ≫ (h.filt_compat s k).choose) =
        ((g.filt_compat (s + 1) k).choose ≫ (h.filt_compat (s + 1) k).choose) ≫
          Subobject.ofLE (FC₃.fil (s + 1) k) (FC₃.fil s k) (FC₃.fil_anti s k) := by
    intro s k
    rw [← Category.assoc, hwg s k, Category.assoc, hwh s k]
    exact (Category.assoc _ _ _).symm
  -- 把左端的提升族（`(comp g h).filt_compat` 的 choose）经 hlift 换成显式复合提升，
  -- 目标即化为广义复合引理的输出形状。
  rw [FilteredComplexMorphism.assocGradedMapOfMap_congr
    (fun s k => by
      apply (cancel_mono ((FC₃.fil s k).arrow)).mp
      simp only [Category.assoc, Subobject.ofLE_arrow]
      rw [((FilteredComplexMorphism.comp g h).filt_compat s k).choose_spec,
        ((FilteredComplexMorphism.comp g h).filt_compat (s + 1) k).choose_spec,
        ← Category.assoc, Subobject.ofLE_arrow])
    hwφ hlift s k]
  exact FilteredComplexMorphism.assocGradedMapOfMap_comp
    (fun s k => (g.filt_compat s k).choose) (fun s k => (h.filt_compat s k).choose)
    hwg hwh hwφ s k

/-- 复合过滤复形态射诱导复合谱序列态射（φ 分量为关联分次上映射的复合）。 -/
theorem FilteredComplexMorphism.toSpectralSequenceMorphism_comp
    {X Y Z : BoundedFilteredComplex C} (g : X ⟶ Y) (h : Y ⟶ Z) :
    (FilteredComplexMorphism.toSpectralSequenceMorphism (g ≫ h)).φ =
      fun k => (FilteredComplexMorphism.toSpectralSequenceMorphism g).φ k ≫
        (FilteredComplexMorphism.toSpectralSequenceMorphism h).φ k := by
  funext ⟨s, k⟩
  exact FilteredComplexMorphism.assocGradedMap_comp g h s k

/-- **toSS 函子**：有界过滤复形范畴到谱序列范畴，
    对象送至 `toSpectralSequence`，态射送至诱导的谱序列态射。 -/
noncomputable def toSS : BoundedFilteredComplex C ⥤ SpectralSequence C (ℤ × ℤ) where
  obj X := X.FC.toSpectralSequence X.bnd
  map := FilteredComplexMorphism.toSpectralSequenceMorphism
  map_id X := SpectralSequenceMorphism.ext
    (FilteredComplexMorphism.toSpectralSequenceMorphism_id X)
  map_comp g h := SpectralSequenceMorphism.ext
    (FilteredComplexMorphism.toSpectralSequenceMorphism_comp g h)

/-! ### convSS ⥤ 有界过滤复形 函子 -/

/-- 收敛谱序列 `X` 在茎次数 `t` 处的**自身两项有界过滤复形**
    `A(t) ⟶[𝟙] A(t)`（恒等映射的两项复形，过滤为 `X.F`），
    作为有界过滤复形范畴的对象。 -/
noncomputable def selfComplex
    (X : ConvergingSS C ω ω') (hb : X.F.IsBounded) (t : ω') :
    BoundedFilteredComplex C :=
  ⟨underlyingComplex (fun (k' : ω') => 𝟙 (X.A k'))
      (fun (s : ℤ) (k' : ω') => X.F.fcId s k') t,
    underlyingComplexBounded (F₁ := X.F) (F₂ := X.F) (fun (k' : ω') => 𝟙 (X.A k'))
      (fun (s : ℤ) (k' : ω') => X.F.fcId s k') t hb hb⟩

/-- 收敛谱序列之间的态射诱导的**两复形过滤复形态射**：
    次数 `1` 与次数 `0` 处均取 `cm.aMap t`，其余次数取 `0`；
    微分交换由两项复形微分的定义（其余次数微分为 `0`）逐情况验证；
    保过滤性在次数 `1` 由 `F₁.fcId`、次数 `0` 由 `cm.filtration_compat` 给出。
    这里不能在次数 `1` 取恒等：源和目标分别是 `X.A t` 与 `Y.A t`。 -/
noncomputable def toFCMorphism
    {X Y : ConvergingSS C ω ω'} (cm : X ⟶ Y)
    (hbX : X.F.IsBounded) (hbY : Y.F.IsBounded) (t : ω') :
    selfComplex X hbX t ⟶ selfComplex Y hbY t := by
  let component : ∀ k : ℤ,
      (selfComplex X hbX t).FC.A k ⟶ (selfComplex Y hbY t).FC.A k := fun k =>
    if h₁ : k = 1 then
      eqToHom (by simp [selfComplex, underlyingComplex, twoTermObj, h₁]) ≫
        cm.aMap t ≫
          eqToHom (by simp [selfComplex, underlyingComplex, twoTermObj, h₁])
    else if h₀ : k = 0 then
      eqToHom (by simp [selfComplex, underlyingComplex, twoTermObj, h₀]) ≫
        cm.aMap t ≫
          eqToHom (by simp [selfComplex, underlyingComplex, twoTermObj, h₀])
    else 0
  refine
    { f := component
      comm_d := ?_
      filt_compat := ?_ }
  · intro k
    by_cases h₁ : k = 1
    · subst k
      simp [component, selfComplex, underlyingComplex, twoTermDiff, twoTermObj]
    · simp [component, selfComplex, underlyingComplex, twoTermDiff, h₁]
  · intro s k
    by_cases h₁ : k = 1
    · subst k
      simpa [component, selfComplex, underlyingComplex, twoTermFil, twoTermObj] using
        cm.filtration_compat s t
    · by_cases h₀ : k = 0
      · subst k
        simpa [component, selfComplex, underlyingComplex, twoTermFil, twoTermObj] using
          cm.filtration_compat s t
      · refine ⟨0, ?_⟩
        simp [component, selfComplex, underlyingComplex, twoTermFil, twoTermObj, h₁, h₀]

/-- 辅助引理：恒等收敛态射经 `toFCMorphism` 得到的 `f` 分量
    逐次数等于有界过滤复形范畴恒等态射的 `f` 分量。
    次数 `1` / `0` 处两边都是 `eqToHom ≫ 𝟙 ≫ eqToHom`（`aMap` 在
    恒等态射下为 `𝟙`），其余次数两边都是 `0`。 -/
private theorem toFCMorphism_id_f (X : ConvergingSS C ω ω')
    (hb : X.F.IsBounded) (t : ω') (k : ℤ) :
    (toFCMorphism (𝟙 X) hb hb t).f k =
      (𝟙 (selfComplex X hb t) : FilteredComplexMorphism
        (selfComplex X hb t).FC (selfComplex X hb t).FC).f k := by
  unfold toFCMorphism
  have ha : (𝟙 X : ConvergenceMorphism X.conv X.conv).aMap t = 𝟙 (X.A t) := rfl
  show (fun k : ℤ =>
      if h₁ : k = 1 then
        eqToHom (by simp [underlyingComplex, twoTermObj, h₁]) ≫ (𝟙 (X.A t)) ≫
          eqToHom (by simp [underlyingComplex, twoTermObj, h₁])
      else if h₀ : k = 0 then
        eqToHom (by simp [underlyingComplex, twoTermObj, h₀]) ≫ (𝟙 (X.A t)) ≫
          eqToHom (by simp [underlyingComplex, twoTermObj, h₀])
      else 0) k =
    (FilteredComplexMorphism.f
      (𝟙 (underlyingComplex (fun (k' : ω') => 𝟙 (X.A k'))
        (fun (s : ℤ) (k' : ω') => X.F.fcId s k') t) :
        FilteredComplexMorphism
          (underlyingComplex (fun (k' : ω') => 𝟙 (X.A k'))
            (fun (s : ℤ) (k' : ω') => X.F.fcId s k') t)
          (underlyingComplex (fun (k' : ω') => 𝟙 (X.A k'))
            (fun (s : ℤ) (k' : ω') => X.F.fcId s k') t))) k
  by_cases h₁ : k = 1
  · subst k
    show (eqToHom (show twoTermObj (X.A t) (X.A t) 1 = X.A t by
            simp [twoTermObj]) ≫ 𝟙 (X.A t) ≫
          eqToHom (show (X.A t) = twoTermObj (X.A t) (X.A t) (1 - 1) by
            simp [twoTermObj])) =
      (FilteredComplexMorphism.f
        (𝟙 (underlyingComplex (fun (k' : ω') => 𝟙 (X.A k'))
          (fun (s : ℤ) (k' : ω') => X.F.fcId s k') t) :
          FilteredComplexMorphism
            (underlyingComplex (fun (k' : ω') => 𝟙 (X.A k'))
              (fun (s : ℤ) (k' : ω') => X.F.fcId s k') t)
            (underlyingComplex (fun (k' : ω') => 𝟙 (X.A k'))
              (fun (s : ℤ) (k' : ω') => X.F.fcId s k') t))) 1
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  · by_cases h₀ : k = 0
    · subst k
      show (fun k : ℤ =>
        if h₁ : k = 1 then
          eqToHom (show twoTermObj (X.A t) (X.A t) 1 = X.A t by
            simp [twoTermObj]) ≫ (𝟙 (X.A t)) ≫
          eqToHom (show twoTermObj (X.A t) (X.A t) 1 = X.A t by
            simp [twoTermObj])
        else if h₀ : k = 0 then
          eqToHom (show twoTermObj (X.A t) (X.A t) 0 = X.A t by
            simp [twoTermObj]) ≫ (𝟙 (X.A t)) ≫
          eqToHom (show twoTermObj (X.A t) (X.A t) 0 = X.A t by
            simp [twoTermObj])
        else 0) 0 =
        (FilteredComplexMorphism.f
          (𝟙 (underlyingComplex (fun (k' : ω') => 𝟙 (X.A k'))
            (fun (s : ℤ) (k' : ω') => X.F.fcId s k') t) :
            FilteredComplexMorphism
              (underlyingComplex (fun (k' : ω') => 𝟙 (X.A k'))
                (fun (s : ℤ) (k' : ω') => X.F.fcId s k') t)
              (underlyingComplex (fun (k' : ω') => 𝟙 (X.A k'))
                (fun (s : ℤ) (k' : ω') => X.F.fcId s k') t))) 0
      simp only [dif_pos, eqToHom_refl, Category.id_comp, Category.comp_id]
      rfl
    · -- 其余次数：两侧都是零映射（左侧 `dite` 落到 `else 0` 分支，
      -- 右侧 `𝟙` 的 `f` 分量在 `⊥_ C` 与 `⊥_ C` 之间也是零）。
      dsimp only
      rw [dif_neg h₁, dif_neg h₀]
      -- 右侧 `𝟙` 的 `f` 分量两侧都是 `twoTermObj … k = ⊥_ C`，零对象上恒等映射为零。
      have hZ : IsZero (twoTermObj (X.A t) (X.A t) k) := by
        rw [twoTermObj_other (X.A t) (X.A t) k h₁ h₀]
        exact (initialIsInitial (C := C)).isZero
      have hid := hZ.eq_of_src (𝟙 (twoTermObj (X.A t) (X.A t) k))
        (0 : twoTermObj (X.A t) (X.A t) k ⟶ twoTermObj (X.A t) (X.A t) k)
      -- 逐步把两侧换到同一形状：先证右侧的 `f k` 就是 `𝟙 (twoTermObj … k)`。
      show 0 = (FilteredComplexMorphism.f
        (𝟙 (underlyingComplex (fun (k' : ω') => 𝟙 (X.A k'))
          (fun (s : ℤ) (k' : ω') => X.F.fcId s k') t) :
          FilteredComplexMorphism
            (underlyingComplex (fun (k' : ω') => 𝟙 (X.A k'))
              (fun (s : ℤ) (k' : ω') => X.F.fcId s k') t)
            (underlyingComplex (fun (k' : ω') => 𝟙 (X.A k'))
              (fun (s : ℤ) (k' : ω') => X.F.fcId s k') t))) k
      rw [← hid]
      rfl

/-- 辅助引理：复合收敛态射经 `toFCMorphism` 得到的 `f` 分量
    逐次数等于两次 `toFCMorphism` 的 `f` 分量的复合。
    次数 `1` / `0` 处两边都是 `eqToHom ≫ (aMap f ≫ aMap g) ≫ eqToHom`，
    其余次数两边都是 `0`。 -/
private theorem toFCMorphism_comp_f {X Y Z : ConvergingSS C ω ω'}
    (hbX : X.F.IsBounded) (hbY : Y.F.IsBounded) (hbZ : Z.F.IsBounded)
    (f : X ⟶ Y) (g : Y ⟶ Z) (t : ω') (k : ℤ) :
    (toFCMorphism (f ≫ g) hbX hbZ t).f k =
      (CategoryStruct.comp
        (toFCMorphism f hbX hbY t : FilteredComplexMorphism
          (selfComplex X hbX t).FC (selfComplex Y hbY t).FC)
        (toFCMorphism g hbY hbZ t : FilteredComplexMorphism
          (selfComplex Y hbY t).FC (selfComplex Z hbZ t).FC)).f k := by
  -- 先固定复形次数，再化简选中的分支。不能在这里先对
  -- `(f ≫ g).aMap` 做全局 `rw`：未化简的两个依赖 `if` 分支同时
  -- 含有 `eqToHom`，会让 `isDefEq` 反复展开巨大的源、目标类型。
  by_cases h₁ : k = 1
  · subst k
    unfold toFCMorphism
    simp only [dif_pos, Category.assoc, CategoryStruct.comp]
    show (eqToHom (show twoTermObj (X.A t) (X.A t) 1 = X.A t by
            simp [twoTermObj]) ≫ f.aMap t ≫ g.aMap t ≫
          eqToHom (show (Z.A t) = twoTermObj (Z.A t) (Z.A t) (1 - 1) by
            simp [twoTermObj])) =
      eqToHom (show twoTermObj (X.A t) (X.A t) 1 = X.A t by
            simp [twoTermObj]) ≫ f.aMap t ≫
        eqToHom (show (Y.A t) = twoTermObj (Y.A t) (Y.A t) (1 - 1) by
            simp [twoTermObj]) ≫
        (eqToHom (show twoTermObj (Y.A t) (Y.A t) 1 = Y.A t by
            simp [twoTermObj]) ≫ g.aMap t ≫
          eqToHom (show (Z.A t) = twoTermObj (Z.A t) (Z.A t) (1 - 1) by
            simp [twoTermObj]))
    rw [← Category.assoc, ← Category.assoc, ← Category.assoc, ← Category.assoc]
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  · by_cases h₀ : k = 0
    · subst k
      unfold toFCMorphism
      simp only [dif_neg (by omega), dif_pos, Category.assoc, CategoryStruct.comp]
      show (eqToHom (show twoTermObj (X.A t) (X.A t) 0 = X.A t by
              simp [twoTermObj]) ≫ f.aMap t ≫ g.aMap t ≫
            eqToHom (show (Z.A t) = twoTermObj (Z.A t) (Z.A t) 0 by
              simp [twoTermObj])) =
        eqToHom (show twoTermObj (X.A t) (X.A t) 0 = X.A t by
              simp [twoTermObj]) ≫ f.aMap t ≫
          eqToHom (show (Y.A t) = twoTermObj (Y.A t) (Y.A t) 0 by
              simp [twoTermObj]) ≫
          (eqToHom (show twoTermObj (Y.A t) (Y.A t) 0 = Y.A t by
              simp [twoTermObj]) ≫ g.aMap t ≫
            eqToHom (show (Z.A t) = twoTermObj (Z.A t) (Z.A t) 0 by
              simp [twoTermObj]))
      rw [← Category.assoc, ← Category.assoc, ← Category.assoc, ← Category.assoc]
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    · -- 三个分量分别化简，避免一次 `unfold` 同时展开
      -- 复合态射两边的全部依赖分支。
      have hfg : (toFCMorphism (f ≫ g) hbX hbZ t).f k = 0 := by
        unfold toFCMorphism
        dsimp only
        rw [dif_neg h₁, dif_neg h₀]
      have hf : (toFCMorphism f hbX hbY t).f k = 0 := by
        unfold toFCMorphism
        dsimp only
        rw [dif_neg h₁, dif_neg h₀]
      have hg : (toFCMorphism g hbY hbZ t).f k = 0 := by
        unfold toFCMorphism
        dsimp only
        rw [dif_neg h₁, dif_neg h₀]
      rw [hfg]
      change 0 = (toFCMorphism f hbX hbY t).f k ≫
        (toFCMorphism g hbY hbZ t).f k
      rw [hf, hg, zero_comp]

/-- **convSS ⥤ 有界过滤复形函子**：收敛谱序列 `X` 在每个茎次数 `t` 处
    送至其自身的两项复形 `A(t) ⟶[𝟙] A(t)`；
    态射 `cm : X ⟶ Y` 送至 `toFCMorphism cm t`。
    函子性（map_id / map_comp）由 `FilteredComplexMorphism.ext`
    归约到 `f` 分量后引用上面两条辅助引理。 -/
noncomputable def convSSToFC
    (hb : ∀ X : ConvergingSS C ω ω', X.F.IsBounded) (t : ω') :
    ConvergingSS C ω ω' ⥤ BoundedFilteredComplex C where
  obj X := selfComplex X (hb X) t
  map cm := toFCMorphism cm (hb _) (hb _) t
  map_id X := FilteredComplexMorphism.ext
    (funext fun k => toFCMorphism_id_f X (hb X) t k)
  map_comp f g := FilteredComplexMorphism.ext
    (funext fun k => toFCMorphism_comp_f (hb _) (hb _) (hb _) f g t k)

/-! ### ESS 函子：两个函子的复合 -/

/-- **ESS 函子**：`convSSToFC t ⋙ toSS` 的复合，
    即收敛谱序列 `X` 在茎次数 `t` 处送至其自身两项复形 `A(t) ⟶[𝟙] A(t)`
    的谱序列（extension spectral sequence）。 -/
noncomputable def ESSFunctor
    (hb : ∀ X : ConvergingSS C ω ω', X.F.IsBounded) (t : ω') :
    ConvergingSS C ω ω' ⥤ SpectralSequence C (ℤ × ℤ) :=
  convSSToFC (C := C) hb t ⋙ toSS

end KIPBase.SpectralSequence
